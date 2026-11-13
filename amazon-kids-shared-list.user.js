// ==UserScript==
// @name         Amazon Kids 共有中コンテンツ抽出
// @namespace    https://example.invalid/akids-shared-list
// @version      0.11.1
// @description  Parent Dashboard「アプリとコンテンツの管理」で共有中(スイッチON)の項目を抽出・表示し、一括で共有解除する
// @match        https://parents.amazon.co.jp/*
// @match        https://parents.amazon.com/*
// @match        https://parents.amazon.co.uk/*
// @match        https://parents.amazon.de/*
// @match        https://parents.amazon.ca/*
// @include      /^https://parents\.amazon\.[a-z.]+/.*$/
// @grant        none
// @run-at       document-idle
// ==/UserScript==

/*
 * 仕組み(特定のAPIやクラス名に依存しないヒューリスティック方式)
 *  - ページ内のトグル候補 (input[type=checkbox], [role=switch], [aria-checked], [aria-pressed]) を探す
 *  - 各トグルから親要素をたどり「トグルを1つだけ含む最大の祖先」を1行(1コンテンツ)とみなす
 *  - トグルがONの行を記録する。仮想スクロール(画面外の行がDOMから消える方式)でも
 *    スクロール中に見えた行を逐次記録するので、最後まで流せば全件拾える
 *  - 無限スクロールのリストを自動スクロールで最後まで読み込む
 *
 * ユーザースクリプトマネージャ(Violentmonkey/Tampermonkey)に入れても、
 * 開発者ツールのコンソールに貼り付けても動くように書いてある。
 */
(() => {
  'use strict';
  if (window.__akidsSharedList) { window.__akidsSharedList.show(); return; }

  const SWITCH_SEL = 'input[type="checkbox"], [role="switch"], [aria-checked], [aria-pressed]';
  // ナビゲーション等の領域。ここにあるトグル風の要素(「ホーム」ボタン等)は対象外
  const NAV_SEL = 'nav, header, footer, [role="navigation"], [role="menubar"], [role="menu"], ' +
    '[role="tablist"], [role="banner"], [role="contentinfo"], [id^="pd-nav"]';
  const STEP_WAIT_MS = 700;   // 下端付近での1スクロールごとの待ち時間。読み込みが追いつかなければ増やす
  const FAST_STEP_MS = 150;   // 読み込み済みの範囲を進むときの待ち時間(再開時の早送りなど)
  const LS_OP = 'akids-lastop', LS_KEEP = 'akids-keep';  // 中断した操作と「残すタイトル」の保存先
  const IDLE_SEC_DEFAULT = 20; // 下端で新しい項目が増えないままこの秒数経ったら終了(パネルで変更可)
  const LOADING_MAX_SEC = 120; // 読み込み中の表示が出ている間は最大この秒数まで待つ
  const NUDGE_EVERY_MS = 4000; // 下端で待っている間、この間隔で少し戻して再度下端へ(読み込みの再発火)
  const BULK_WAIT_MS = 400;   // 一括解除で1件ごとに空ける間隔(サーバへの送信が追いつくように)
  const BULK_VERIFY_MS = 8000;// クリック後、状態が変わるのを待つ最大時間
  const RETRY_VERIFY_MS = 15000; // 最後の再試行で待つ最大時間
  const CLICK_INTERVAL_MS = 300; // 一括操作でクリックとクリックの間に空ける時間
  const MAX_INFLIGHT = 8;        // 反映を確認できていないクリックがこの件数に達したら、減るまで待つ
  const PENDING_TIMEOUT_MS = 15000; // クリック後この時間内に反映されなければ「未確認」として最後に再確認
  const BACKOFF_STEP_MS = 500;   // 失敗するたびに間隔をこれだけ延ばす(成功で少しずつ戻す)
  const BACKOFF_MAX_MS = 4000;
  const BULK_MAX_CONSEC_FAIL = 5; // この件数連続で切り替わらなければ中断

  const state = {
    invert: false,       // ON/OFF判定を反転(ONがブロックを意味するUIだった場合用)
    hideOff: false,      // OFFの行をページ上で非表示にする
    lite: true,
    idleSec: IDLE_SEC_DEFAULT,          // 画面外の行の描画を省略してページを軽くする
    running: false,
    bulk: false,         // 一括共有解除の実行中
    bulkHref: '',        // 一括操作開始時のURL(変わったら中止)
    navAbort: false,
    extraWait: 0,        // 失敗時に自動で延ばす待ち時間
    pending: null,       // 確認済みの解除対象(トグル要素の配列)
    found: new Map(),    // key -> {title, sub, img}  (現在ONと判定された項目)
    seen: new Set(),     // これまでに見た全項目のkey
  };

  // 処理済みトグルのキャッシュ。各トグルの行・タイトル判定は初回の1回だけ行う
  let cache = new WeakMap();    // sw -> {row, key, info, on}
  let rejected = new WeakSet(); // コンテンツ行でないと判定したトグル風要素
  let live = [];                // 処理済みでまだDOMに残っているトグル
  // コンテンツ行の構造モデル(最初に多数決で学習)。null の間は何も処理しない
  //   type: トグルの種類 / depth: トグルから行要素までの階層数 / parentSig: 行の親要素の tag.class
  let model = null;
  const items = new Map();      // key -> パネルの<li>

  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

  // ---------- パネル ----------
  const style = document.createElement('style');
  style.textContent = `
    [data-akids-hide] { display: none !important; }
    [data-akids-lite] { content-visibility: auto; contain-intrinsic-size: auto 120px; }
    #akids-panel { position: fixed; right: 12px; bottom: 12px; z-index: 2147483647;
      width: 360px; max-height: 70vh; display: flex; flex-direction: column;
      background: #fff; color: #111; border: 1px solid #888; border-radius: 8px;
      box-shadow: 0 4px 16px rgba(0,0,0,.25); font: 13px/1.4 sans-serif; }
    #akids-panel header { padding: 6px 10px; background: #232f3e; color: #fff;
      border-radius: 8px 8px 0 0; display: flex; justify-content: space-between; cursor: move; }
    #akids-panel .body { padding: 8px 10px; overflow: auto; }
    #akids-panel button { margin: 2px 4px 2px 0; padding: 3px 8px; cursor: pointer; }
    #akids-panel label { display: block; margin: 2px 0; }
    #akids-panel .status { margin: 6px 0; color: #555; white-space: pre-wrap; }
    #akids-panel ol { margin: 4px 0 0 1.4em; padding: 0; }
    #akids-panel li { margin: 2px 0; }
    #akids-panel li small { color: #777; }
    #akids-panel.min .body { display: none; }
    #akids-panel details { margin: 6px 0; padding: 4px 6px; border: 1px solid #ccc; border-radius: 4px; }
    #akids-panel textarea { width: 100%; box-sizing: border-box; height: 70px; font-size: 12px; }
    #akids-panel button.danger { background: #c40000; color: #fff; border: 1px solid #900; }
    #akids-panel button:disabled { opacity: .5; cursor: default; }
  `;
  document.head.appendChild(style);

  const panel = document.createElement('div');
  panel.id = 'akids-panel';
  panel.innerHTML = `
    <header><b>共有中コンテンツ抽出</b><span><a href="#" data-a="min" style="color:#fff">_</a>&nbsp;
      <a href="#" data-a="close" style="color:#fff">×</a></span></header>
    <div class="body">
      <div>
        <button data-a="auto">全件読み込み開始</button>
        <button data-a="scan">今の画面をスキャン</button>
      </div>
      <div>
        <button data-a="allOn" class="danger">全件共有ON</button>
        <button data-a="allOff" class="danger">全件共有OFF</button>
      </div>
      <div>
        <button data-a="copy">一覧をコピー(TSV)</button>
        <button data-a="clear">記録をクリア</button>
        <button data-a="diag">診断</button>
        <button data-a="test1">1件テスト</button>
      </div>
      <label><input type="checkbox" data-o="hideOff"> OFF(非共有)の行をページ上で隠す</label>
      <label><input type="checkbox" data-o="invert"> ON/OFF判定を反転</label>
      <label><input type="checkbox" data-o="lite" checked> 画面外の行の描画を省略(軽量化)</label>
      <label>読み込み待ち: <input type="number" data-n="idleSec" min="5" max="600" value="${IDLE_SEC_DEFAULT}" style="width:4em"> 秒(増えなければ終了)</label>
      <details>
        <summary><b>一括共有解除</b></summary>
        <div>共有のまま残すタイトル(1行に1つ・部分一致):</div>
        <textarea data-k="keep" placeholder="例:&#10;はらぺこ&#10;図鑑"></textarea>
        <div>
          <button data-a="preview">対象を確認</button>
          <button data-a="bulk" class="danger" disabled>共有解除を実行</button>
        </div>
      </details>
      <div class="resume" style="display:none; margin:6px 0; padding:4px 6px; background:#fff4d6; border:1px solid #e0b000; border-radius:4px">
        <span class="resume-msg"></span><br>
        <button data-a="resume" class="danger">続きから再開</button>
        <button data-a="discard">破棄</button>
      </div>
      <div class="status"></div>
      <ol></ol>
    </div>`;
  document.body.appendChild(panel);
  const $status = panel.querySelector('.status');
  const $list = panel.querySelector('ol');
  const $auto = panel.querySelector('[data-a="auto"]');
  const $bulk = panel.querySelector('[data-a="bulk"]');
  const $keep = panel.querySelector('[data-k="keep"]');
  const $resumeBox = panel.querySelector('.resume');
  const $resume = panel.querySelector('[data-a="resume"]');
  const $allOn = panel.querySelector('[data-a="allOn"]');
  const $allOff = panel.querySelector('[data-a="allOff"]');
  const ALL_LABEL = { on: '全件共有ON', off: '全件共有OFF' };

  // ---------- 判定ロジック ----------
  // aria-checked はページ(アプリ)側が状態に合わせて描画する値なので、あればこれを優先する。
  // input の .checked はスクリプトのクリックだけで一時的に変わることがあり、保存の確認には使えない
  function rawOn(sw) {
    if (sw.hasAttribute('aria-checked')) return sw.getAttribute('aria-checked') === 'true';
    if (sw.matches('input[type="checkbox"]')) return sw.checked;
    return sw.getAttribute('aria-pressed') === 'true';
  }
  function isOn(sw) {
    const v = rawOn(sw);
    return state.invert ? !v : v;
  }

  // ---------- 通信の記録(保存リクエストが出たか・失敗していないかを確認するため) ----------
  const net = { log: [] };
  function netRec(method, url) {
    const rec = { t: Date.now(), method: String(method || 'GET').toUpperCase(), url: String(url), status: null };
    net.log.push(rec);
    if (net.log.length > 500) net.log.splice(0, net.log.length - 500);
    return rec;
  }
  (() => {
    if (window.__akidsNetHooked) return;
    window.__akidsNetHooked = true;
    const of = window.fetch;
    if (of) {
      window.fetch = function (input, init) {
        const rec = netRec((init && init.method) || (input && input.method), (input && input.url) || input);
        return of.apply(this, arguments).then(
          (res) => { rec.status = res.status; return res; },
          (e) => { rec.status = 'error'; throw e; });
      };
    }
    const XO = XMLHttpRequest.prototype.open, XS = XMLHttpRequest.prototype.send;
    XMLHttpRequest.prototype.open = function (m, u) { this.__akids = [m, u]; return XO.apply(this, arguments); };
    XMLHttpRequest.prototype.send = function () {
      const a = this.__akids || ['GET', ''];
      const rec = netRec(a[0], a[1]);
      this.addEventListener('loadend', () => { rec.status = this.status || 'error'; });
      return XS.apply(this, arguments);
    };
  })();
  // 指定時刻以降の、データを変更する通信(GET以外)
  const writesSince = (t) => net.log.filter((r) => r.t >= t && r.method !== 'GET' && r.method !== 'HEAD');
  const isBad = (r) => r.status === 'error' || (typeof r.status === 'number' && r.status >= 400);

  // 人がマウスで押すのと同じ順でイベントを送る。押す位置は、トグルの中心に実際に表示されている要素
  // (見た目用の要素が重なっていることが多い)。ただし同じ行の中の要素に限る
  function realClick(el) {
    const c = cache.get(el);
    const row = c ? c.row : el.parentElement;
    const box = (el.getClientRects().length ? el : el.closest('label')) || el;
    if (box.scrollIntoView) box.scrollIntoView({ block: 'center' });
    const r = box.getBoundingClientRect();
    const x = r.left + r.width / 2, y = r.top + r.height / 2;
    let hit = (r.width && r.height && document.elementFromPoint) ? document.elementFromPoint(x, y) : null;
    if (!hit || panel.contains(hit) || !row.contains(hit)) hit = el;
    const o = { bubbles: true, cancelable: true, composed: true, view: window, clientX: x, clientY: y, button: 0 };
    const po = Object.assign({ pointerId: 1, pointerType: 'mouse', isPrimary: true }, o);
    if (window.PointerEvent) hit.dispatchEvent(new PointerEvent('pointerdown', po));
    hit.dispatchEvent(new MouseEvent('mousedown', Object.assign({ buttons: 1 }, o)));
    if (window.PointerEvent) hit.dispatchEvent(new PointerEvent('pointerup', po));
    hit.dispatchEvent(new MouseEvent('mouseup', o));
    hit.click();
    return hit;
  }

  // 入れ子になったトグル候補(例: role=switch の中の input)は外側だけ採用
  function findSwitches() {
    // 見た目を作り込んだトグルは input 自体が非表示のことが多いので、親labelが見えていれば可視扱い
    const visible = (el) => el.getClientRects().length > 0 ||
      (el.closest('label') && el.closest('label').getClientRects().length > 0);
    return [...document.querySelectorAll(SWITCH_SEL)].filter((el) => isCandidate(el) && visible(el));
  }

  function swType(el) {
    return el.matches('input[type="checkbox"]') ? 'checkbox'
      : el.getAttribute('role') === 'switch' ? 'switch'
      : el.hasAttribute('aria-checked') ? 'aria-checked' : 'aria-pressed';
  }

  const sigOf = (el) => el.tagName + '.' + (typeof el.className === 'string' ? el.className : '');

  // 候補から外すもの: パネル内 / 入れ子の内側 / ナビゲーション内 / リンク
  function isCandidate(el) {
    return !panel.contains(el) &&
      !(el.parentElement && el.parentElement.closest(SWITCH_SEL)) &&
      !el.closest(NAV_SEL) && !el.closest('a[href]');
  }

  // 行構造を多数決で学習する。ナビゲーション等の少数の要素に引きずられないよう、
  // 「同じ種類のトグル・同じ深さ・同じ親要素」を持つグループのうち最大のものを採用する
  function learn(cands) {
    const outer = new Set(cands);
    const groups = new Map();
    for (const sw of cands.slice(0, 60)) {
      const { row, depth } = rowOfSlow(sw, outer);
      if (!row.parentElement) continue;
      const g = { type: swType(sw), depth, parentSig: sigOf(row.parentElement) };
      const k = g.type + '|' + g.depth + '|' + g.parentSig;
      const cur = groups.get(k) || Object.assign(g, { n: 0 });
      cur.n++;
      groups.set(k, cur);
    }
    let best = null;
    for (const g of groups.values()) if (!best || g.n > best.n) best = g;
    return best && best.n >= 3 ? best : null;
  }

  // 学習済みモデルに合うトグルなら行要素を返し、合わなければ null
  function rowFor(sw) {
    if (!model || swType(sw) !== model.type) return null;
    const row = rowOf(sw);
    return row.parentElement && sigOf(row.parentElement) === model.parentSig ? row : null;
  }

  function countIn(node, outer) {
    let n = 0;
    for (const el of node.querySelectorAll(SWITCH_SEL)) {
      if (outer.has(el) && ++n > 1) break;
    }
    return n;
  }

  // 正確だが遅い行判定(リスト全体を走査する)。学習と診断にだけ使う
  function rowOfSlow(sw, outer) {
    let row = sw, depth = 0, d = 0;
    for (let p = sw.parentElement; p && p !== document.body; p = p.parentElement) {
      d++;
      if (countIn(p, outer) > 1) break;
      row = p; depth = d;
    }
    return { row, depth };
  }

  // 高速な行判定: 学習した階層数だけ親をたどる
  function rowOf(sw) {
    let row = sw;
    for (let i = 0; i < model.depth && row.parentElement && row.parentElement !== document.body; i++) {
      row = row.parentElement;
    }
    return row;
  }

  function infoOf(row, sw) {
    // innerTextはレイアウト計算を伴うのでtextContent系で取る
    const texts = [];
    const walker = document.createTreeWalker(row, NodeFilter.SHOW_TEXT);
    for (let n = walker.nextNode(); n && texts.length < 3; n = walker.nextNode()) {
      const t = n.nodeValue.trim();
      if (t && !(n.parentElement && n.parentElement.closest('script, style'))) texts.push(t);
    }
    const imgEl = row.querySelector('img');
    const alt = imgEl && imgEl.alt ? imgEl.alt.trim() : '';
    const aria = (sw.getAttribute('aria-label') || '').trim();
    return {
      title: texts[0] || alt || aria || '(タイトル不明)',
      sub: texts.slice(1, 3).join(' / '),
      img: imgEl ? (imgEl.currentSrc || imgEl.src || '') : '',
    };
  }

  function applyRow(c) {
    if (state.hideOff && !c.on) c.row.setAttribute('data-akids-hide', '');
    else c.row.removeAttribute('data-akids-hide');
    if (state.lite) c.row.setAttribute('data-akids-lite', '');
    else c.row.removeAttribute('data-akids-lite');
  }

  function setFound(c) {
    if (c.on) {
      if (!state.found.has(c.key)) {
        state.found.set(c.key, c.info);
        const li = document.createElement('li');
        li.textContent = c.info.title + ' ';
        if (c.info.sub) {
          const sm = document.createElement('small');
          sm.textContent = c.info.sub;
          li.appendChild(sm);
        }
        $list.appendChild(li);
        items.set(c.key, li);
      }
    } else if (state.found.delete(c.key)) {
      const li = items.get(c.key);
      if (li) li.remove();
      items.delete(c.key);
    }
  }

  // 新しく現れたトグルだけを処理し、既存分はON/OFFの読み直しだけ行う
  function scan() {
    const fresh = [];
    for (const el of document.querySelectorAll(SWITCH_SEL)) {
      if (rejected.has(el) || cache.has(el) || !isCandidate(el)) continue;
      fresh.push(el);
    }
    // 見た目を作り込んだトグルは input 自体が非表示のことが多いので、親labelが見えていれば可視扱い
    const visible = (el) => el.getClientRects().length > 0 ||
      (el.closest('label') && el.closest('label').getClientRects().length > 0);
    const newSws = fresh.filter(visible);

    if (!model) {
      model = learn(newSws);
      if (!model) return live.length;  // まだ行構造を判定できない(コンテンツ行が3件未満など)
      console.log('[akids] 行構造を学習:', model);
    }

    for (const sw of newSws) {
      const row = rowFor(sw);
      if (!row) { rejected.add(sw); continue; }  // コンテンツ行ではない(ナビ等)
      const info = infoOf(row, sw);
      const c = { row, info, key: info.title + '\t' + info.img, on: isOn(sw) };
      cache.set(sw, c);
      live.push(sw);
      state.seen.add(c.key);
      setFound(c);
      applyRow(c);
    }

    // 既存分: DOMから消えたもの(仮想スクロール)は外し、ON/OFFの変化だけ反映
    live = live.filter((sw) => sw.isConnected);
    for (const sw of live) {
      const c = cache.get(sw);
      const on = isOn(sw);
      if (on !== c.on) { c.on = on; setFound(c); applyRow(c); }
    }
    setStatus();
    return live.length;
  }

  // オプション変更時: 全件の状態を付け直す
  function reapply() {
    for (const sw of live) {
      const c = cache.get(sw);
      c.on = isOn(sw);
      setFound(c);
      applyRow(c);
    }
    setStatus();
  }

  function setStatus(extra) {
    $status.textContent =
      `共有中: ${state.found.size} 件 / 確認済み: ${state.seen.size} 件` +
      (state.running ? '\n読み込み中…(停止ボタンで中断)' : '') +
      (extra ? '\n' + extra : '');
  }

  // ---------- 自動スクロール ----------
  function findScroller() {
    // まずトグルの祖先からスクロール可能な要素を探す(全要素の走査は重いので後回し)
    const sw = live.find((x) => x.isConnected) || document.querySelector(SWITCH_SEL);
    for (let p = sw && sw.parentElement; p && p !== document.body; p = p.parentElement) {
      const oy = getComputedStyle(p).overflowY;
      if ((oy === 'auto' || oy === 'scroll') && p.scrollHeight - p.clientHeight > 50) return p;
    }
    if ((document.scrollingElement || document.documentElement).scrollHeight - (document.scrollingElement || document.documentElement).clientHeight > 50) {
      return (document.scrollingElement || document.documentElement);
    }
    let best = null, area = 0;
    for (const el of document.querySelectorAll('body *')) {
      if (panel.contains(el)) continue;
      if (el.scrollHeight - el.clientHeight < 50) continue;
      const oy = getComputedStyle(el).overflowY;
      if (oy !== 'auto' && oy !== 'scroll') continue;
      const a = el.clientWidth * el.clientHeight;
      if (a > area) { area = a; best = el; }
    }
    return best || (document.scrollingElement || document.documentElement);
  }

  // 読み込み中らしき表示(スピナー等)が見えているか
  function isLoading() {
    for (const el of document.querySelectorAll(
      '[aria-busy="true"], [role="progressbar"], [class*="spinner" i], [class*="loading" i], [class*="loader" i]')) {
      if (!panel.contains(el) && el.getClientRects().length > 0) return true;
    }
    return false;
  }

  function newScrollCtx() {
    const sc = findScroller();
    return { sc, lastSeen: state.seen.size, lastH: sc.scrollHeight, lastProgress: Date.now(),
      lastNudge: Date.now(), stuck: 0, idleMs: 0, loading: false };
  }

  // 1ステップ下へスクロールし、続けるべきなら true を返す。
  // 終了判定は「下端にいて、項目数もページの高さも増えない状態が一定時間続いた」とき。
  async function scrollStep(ctx) {
    let sc = ctx.sc;
    const prev = sc.scrollTop;
    sc.scrollTop = prev + Math.max(200, sc.clientHeight * 0.8);
    // 読み込み済みの範囲の途中なら短く、下端付近(続きの読み込みが起きる所)では長めに待つ
    const nearBottom = sc.scrollTop === prev ||
      sc.scrollTop + sc.clientHeight >= sc.scrollHeight - Math.max(400, sc.clientHeight);
    await sleep(nearBottom ? STEP_WAIT_MS : FAST_STEP_MS);
    scan();
    const now = Date.now();
    const atBottom = sc.scrollTop + sc.clientHeight >= sc.scrollHeight - 5;
    if (sc.scrollTop === prev && !atBottom && ++ctx.stuck >= 2) { ctx.sc = sc = findScroller(); ctx.stuck = 0; }
    const progressed = state.seen.size !== ctx.lastSeen || sc.scrollHeight !== ctx.lastH ||
      (!atBottom && sc.scrollTop !== prev);
    ctx.lastSeen = state.seen.size;
    ctx.lastH = sc.scrollHeight;
    if (progressed) {
      ctx.lastProgress = ctx.lastNudge = now;
    } else if (atBottom && now - ctx.lastNudge >= NUDGE_EVERY_MS) {
      // 下端の読み込みトリガーが再発火しない実装への対策: 1画面分戻してから下端へ戻る
      ctx.lastNudge = now;
      sc.scrollTop = Math.max(0, sc.scrollTop - sc.clientHeight);
      await sleep(300);
      sc.scrollTop = sc.scrollHeight;
    }
    ctx.loading = isLoading();
    ctx.idleMs = now - ctx.lastProgress;
    const limit = (ctx.loading ? Math.max(LOADING_MAX_SEC, state.idleSec) : state.idleSec) * 1000;
    return ctx.idleMs < limit;
  }

  function waitNote(ctx) {
    return ctx.idleMs >= 2000
      ? `\n読み込み待ち ${Math.round(ctx.idleMs / 1000)} 秒${ctx.loading ? '(読み込み表示あり)' : ''}` : '';
  }

  async function autoScroll() {
    state.running = true;
    $auto.textContent = '停止';
    scan();
    const ctx = newScrollCtx();
    while (state.running && await scrollStep(ctx)) {
      setStatus(waitNote(ctx).trim());
    }
    const finished = state.running;
    state.running = false;
    $auto.textContent = '全件読み込み開始';
    setStatus(finished ? '最後まで到達しました。' : '中断しました。');
  }

  // 手動スクロールでも記録されるようにDOM変化を監視
  let moTimer = 0;
  const mo = new MutationObserver((muts) => {
    if (state.running || state.bulk || moTimer) return;
    if (muts.every((m) => panel.contains(m.target))) return;  // パネル自身の更新は無視  // 自動スクロール中はループ側でスキャンする
    moTimer = setTimeout(() => { moTimer = 0; scan(); }, 500);
  });
  mo.observe(document.body, { childList: true, subtree: true, attributes: true,
    attributeFilter: ['aria-checked', 'aria-pressed'] });
  document.addEventListener('change', () => setTimeout(() => { if (!state.running) scan(); }, 100), true);

  // ---------- 一括共有解除 ----------
  function keepWords() {
    return $keep.value.split('\n').map((x) => x.trim()).filter(Boolean);
  }

  function preview() {
    scan();
    const keep = keepWords();
    const targets = [], kept = [];
    for (const sw of live) {
      const c = cache.get(sw);
      if (!c || !c.on) continue;
      (keep.some((k) => c.info.title.includes(k)) ? kept : targets).push(sw);
    }
    // 一覧には載っているがDOMから消えている(=操作できない)項目
    const unreachable = state.found.size - targets.length - kept.length;
    state.pending = targets;
    $bulk.disabled = targets.length === 0;
    $bulk.textContent = `共有解除を実行(${targets.length}件)`;
    const show = (arr) => arr.slice(0, 5).map((sw) => '  ・' + cache.get(sw).info.title).join('\n') +
      (arr.length > 5 ? `\n  …ほか${arr.length - 5}件` : '');
    setStatus(`解除対象: ${targets.length} 件\n${show(targets)}\n` +
      `残す(共有のまま): ${kept.length} 件${kept.length ? '\n' + show(kept) : ''}` +
      (unreachable > 0 ? `\n※ ${unreachable} 件はページから消えているため操作できません` : '') +
      (state.seen.size === 0 ? '' : '\n全件読み込みが済んでいることを確認してから実行してください。'));
  }

  // 1件を目標状態に切り替え、実際に変わったか確かめる。戻り値: 'ok' | 'skip' | 'fail'
  // クリック後にページがトグル要素を作り直すことがあるので、
  // 元の要素がDOMから外れていたら aria-label が同じ要素を探して差し替える
  function current(sw) {
    if (sw.isConnected) return sw;
    const al = sw.getAttribute('aria-label');
    if (!al) return null;
    for (const el of document.querySelectorAll(SWITCH_SEL)) {
      if (el.getAttribute('aria-label') === al && isCandidate(el)) return el;
    }
    return null;
  }

  // 差し替わった要素をキャッシュに登録し直す
  function adopt(oldSw, el) {
    if (el === oldSw) return cache.get(el);
    const old = cache.get(oldSw);
    const row = rowFor(el) || old.row;
    const c = { row, info: old.info, key: old.key, on: old.on, failed: old.failed };
    cache.set(el, c);
    live = live.filter((x) => x !== oldSw && x !== el);
    live.push(el);
    return c;
  }

  // 状態が target になるまで最大 ms 待つ。なったら true
  async function waitState(sw, target, ms) {
    for (let t = 0; t < ms; t += 100) {
      await sleep(100);
      const el = current(sw);
      if (el && isOn(el) === target) {
        const c = adopt(sw, el);
        c.on = target; c.failed = false; setFound(c); applyRow(c);
        return true;
      }
    }
    return false;
  }

  // 1件を目標状態に切り替え、実際に変わったか確かめる。戻り値: 'ok' | 'skip' | 'fail'
  async function toggleTo(sw, target, verifyMs = BULK_VERIFY_MS) {
    const c = cache.get(sw);
    const el = current(sw);
    if (!c || !el) return 'fail';
    if (el !== sw) adopt(sw, el);
    const cc = cache.get(el);
    if (isOn(el) === target) { cc.on = target; cc.failed = false; setFound(cc); applyRow(cc); return 'skip'; }
    if (!rowFor(el) || !isCandidate(el)) { cc.failed = true; return 'fail'; }  // 念のため再確認
    realClick(el);
    if (location.href !== state.bulkHref) {  // ページ遷移が起きたら即中止
      state.bulk = false;
      state.navAbort = true;
      console.warn('[akids] ページ遷移を検知したため中止しました:', cc.info.title, el);
      return 'fail';
    }
    if (await waitState(el, target, verifyMs)) {
      state.extraWait = Math.max(0, state.extraWait - 100);
      return 'ok';
    }
    cc.failed = true;
    state.extraWait = Math.min(BACKOFF_MAX_MS, state.extraWait + BACKOFF_STEP_MS);
    console.warn('[akids] 時間内に切り替わりを確認できなかった項目(最後に再確認します):', cc.info.title, el);
    return 'fail';
  }

  // 最後の再確認: 遅れて反映されていればそれで成功、まだなら1回だけ押し直す。
  // 押し直す前に必ず現在の状態を読み直すので、二重に切り替えてしまうことはない
  async function retryFailed(target, list, label) {
    let lateOk = 0, retryOk = 0, still = 0;
    for (let i = 0; i < list.length; i++) {
      if (!state.bulk) break;
      setStatus(`${label}: 切り替わらなかった項目を再確認中… ${i + 1}/${list.length}`);
      const sw = list[i];
      const el = current(sw);
      if (!el) { still++; continue; }
      if (isOn(el) === target) {
        const c = adopt(sw, el); c.on = target; c.failed = false; setFound(c); applyRow(c);
        lateOk++; continue;
      }
      await sleep(1500);
      const r = await toggleTo(el, target, RETRY_VERIFY_MS);
      if (r === 'ok' || r === 'skip') retryOk++;
      else { still++; console.warn('[akids] 再試行でも切り替わらなかった項目:', cache.get(current(el) || el).info.title); }
      await sleep(BULK_WAIT_MS + state.extraWait);
    }
    return { lateOk, retryOk, still };
  }

  const retryNote = (r) => (r.lateOk + r.retryOk + r.still === 0) ? '' :
    `\n再確認: 遅れて反映 ${r.lateOk} / 押し直して成功 ${r.retryOk} / 未解決 ${r.still}` +
    (r.still ? '(コンソールに書名を出力しています)' : '');

  const FAIL_MSG = `${BULK_MAX_CONSEC_FAIL}件連続で切り替わらなかったため中断しました。` +
    '確認ダイアログが出ていないか、ページの状態を確認してください。';

  // ---------- 並行処理(クリックしたら反映を待たずに次へ進み、確認は裏で行う) ----------
  function makePipe(target) {
    return { target, pending: [], keys: new Set(), failedKeys: new Set(), failed: [],
      ok: 0, fail: 0, skip: 0, consec: 0, stopReason: '', t0: Date.now() };
  }

  // 反映待ちのクリックを確認する
  function pipeCheck(pp) {
    const now = Date.now();
    const bad = writesSince(pp.t0).filter(isBad);
    if (bad.length >= 3 && !pp.stopReason) {
      pp.stopReason = `保存用の通信が ${bad.length} 回失敗したため中断しました(例: ${bad[0].status} ${bad[0].method} ${bad[0].url.slice(0, 80)})。`;
    }
    pp.pending = pp.pending.filter((p) => {
      const el = current(p.sw);
      if (el && isOn(el) === pp.target) {
        const c = adopt(p.sw, el);
        c.on = pp.target; c.failed = false; setFound(c); applyRow(c);
        pp.ok++; pp.consec = 0; pp.keys.delete(p.key);
        return false;
      }
      if (now - p.t > PENDING_TIMEOUT_MS) {
        pp.fail++; pp.failed.push(p.sw); pp.failedKeys.add(p.key); pp.keys.delete(p.key);
        console.warn('[akids] 時間内に反映を確認できなかった項目(最後に再確認します):', p.title);
        if (++pp.consec >= BULK_MAX_CONSEC_FAIL) pp.stopReason = FAIL_MSG;
        return false;
      }
      return true;
    });
  }

  // 1件クリックする。処理を続けてよければ true
  async function pipeClick(pp, sw) {
    while (pp.pending.length >= MAX_INFLIGHT) {
      if (!state.bulk) return false;
      await sleep(100);
      pipeCheck(pp);
      if (pp.stopReason) return false;
    }
    if (!state.bulk) return false;
    const el = current(sw);
    if (!cache.get(sw) || !el) return true;
    if (el !== sw) adopt(sw, el);
    const c = cache.get(el);
    if (pp.keys.has(c.key) || pp.failedKeys.has(c.key)) return true;   // 反映待ち・未確認の項目は押さない
    if (isOn(el) === pp.target) { pp.skip++; return true; }
    if (!rowFor(el) || !isCandidate(el)) return true;                 // 念のため再確認
    realClick(el);
    if (location.href !== state.bulkHref) {  // ページ遷移が起きたら即中止
      state.bulk = false;
      state.navAbort = true;
      console.warn('[akids] ページ遷移を検知したため中止しました:', c.info.title, el);
      return false;
    }
    pp.pending.push({ sw: el, key: c.key, title: c.info.title, t: Date.now() });
    pp.keys.add(c.key);
    await sleep(CLICK_INTERVAL_MS);
    pipeCheck(pp);
    return !pp.stopReason;
  }

  // 残っている反映待ちをすべて確認し終えるまで待つ
  async function pipeDrain(pp, label) {
    while (pp.pending.length) {
      setStatus(`${label}: 反映を確認中… 残り ${pp.pending.length} 件`);
      await sleep(200);
      pipeCheck(pp);
    }
  }

  const pipeNote = (pp) => {
    const w = writesSince(pp.t0);
    return `成功 ${pp.ok} / 反映待ち ${pp.pending.length} / 未確認 ${pp.fail}` +
      ` / 保存通信 ${w.length}(失敗 ${w.filter(isBad).length})`;
  };

  function setBusy(busy, activeBtn) {
    for (const b of [$auto, $bulk, $allOn, $allOff, $resume]) {
      if (b !== activeBtn) b.disabled = busy;
    }
    if (!busy) {
      $bulk.disabled = true;
      $bulk.textContent = '共有解除を実行';
      $allOn.textContent = ALL_LABEL.on;
      $allOff.textContent = ALL_LABEL.off;
    }
  }

  async function bulkOff() {
    const list = state.pending || [];
    state.pending = null;
    state.bulk = true;
    state.bulkHref = location.href;
    state.navAbort = false;
    state.extraWait = 0;
    $bulk.textContent = '停止';
    setBusy(true, $bulk);
    const pp = makePipe(false);
    let reason = '';
    for (let i = 0; i < list.length; i++) {
      if (!(await pipeClick(pp, list[i]))) break;
      setStatus(`共有解除中… ${i + 1}/${list.length}(${pipeNote(pp)} / 既にOFF ${pp.skip})`);
    }
    if (state.navAbort) reason = 'ページ遷移を検知したため中止しました。';
    else if (pp.stopReason) reason = pp.stopReason;
    else if (!state.bulk) reason = '中断しました。';
    if (!state.navAbort) await pipeDrain(pp, '共有解除');
    const rr = (!reason && pp.failed.length) ? await retryFailed(false, pp.failed, '共有解除')
      : { lateOk: 0, retryOk: 0, still: 0 };
    state.bulk = false;
    setBusy(false);
    setStatus(`完了: ${pipeNote(pp)} / 既にOFF ${pp.skip}` + retryNote(rr) + (reason ? '\n' + reason : '') +
      '\n念のためページを再読み込みし、もう一度全件読み込みして結果を確認してください。');
  }

  // 全件共有ON/OFF: 先頭から最後までスクロールしながら、見えた項目を順に目標状態へ切り替える。
  // 共有OFFのときは「共有のまま残すタイトル」に一致する項目には触れない。
  // opts.resume: 先頭に戻らず、今のスクロール位置から続ける(ページ再読み込み後は先頭から早送りになる)
  async function setAll(target, opts = {}) {
    const btn = target ? $allOn : $allOff;
    const keep = target ? [] : keepWords();
    saveOp({ target, keep, status: 'running', t: Date.now() });
    $resumeBox.style.display = 'none';
    state.bulk = true;
    state.bulkHref = location.href;
    state.navAbort = false;
    state.extraWait = 0;
    state.pending = null;
    btn.textContent = '停止';
    setBusy(true, btn);
    for (const sw of live) { const c = cache.get(sw); if (c) c.failed = false; }

    if (!opts.resume) {
      const sc0 = findScroller();
      sc0.scrollTop = 0;
      await sleep(STEP_WAIT_MS);
    }
    const ctx = newScrollCtx();
    const pp = makePipe(target);
    const label = target ? '全件共有ON' : '全件共有OFF';
    let reason = '';

    run: while (true) {
      scan();
      let touched = false;
      for (const sw of live.slice()) {
        const c = cache.get(sw);
        if (!c || !sw.isConnected || isOn(sw) === target) continue;
        if (pp.keys.has(c.key) || pp.failedKeys.has(c.key)) continue;
        if (keep.length && keep.some((k) => c.info.title.includes(k))) continue;
        touched = true;
        if (!(await pipeClick(pp, sw))) break run;
        setStatus(`${label}中…(${pipeNote(pp)})`);
      }
      if (!state.bulk) break;
      pipeCheck(pp);
      if (pp.stopReason) break;
      // 切り替え作業に使った時間は「読み込み待ち」に数えない
      if (touched) ctx.lastProgress = ctx.lastNudge = Date.now();
      const cont = await scrollStep(ctx);
      setStatus(`${label}中…(${pipeNote(pp)})` + waitNote(ctx));
      if (!cont) break;
    }
    if (state.navAbort) reason = 'ページ遷移を検知したため中止しました。';
    else if (pp.stopReason) reason = pp.stopReason;
    else if (!state.bulk) reason = '中断しました。';
    if (!state.navAbort) await pipeDrain(pp, label);
    const rr = (!reason && pp.failed.length) ? await retryFailed(target, pp.failed, label)
      : { lateOk: 0, retryOk: 0, still: 0 };
    state.bulk = false;
    setBusy(false);
    saveOp({ target, keep, status: (reason || rr.still) ? 'stopped' : 'done', t: Date.now() });
    showResume();
    setStatus(`${label} 完了: ${pipeNote(pp)}` + retryNote(rr) +
      (keep.length ? `\n「共有のまま残すタイトル」(${keep.length}語)に一致する項目は変更していません。` : '') +
      (reason ? '\n' + reason : '\n最後まで到達しました。') +
      '\n念のためページを再読み込みし、もう一度全件読み込みして結果を確認してください。');
  }

  // ---------- 中断した操作の保存と再開 ----------
  function saveOp(op) {
    try { localStorage.setItem(LS_OP, JSON.stringify(op)); } catch (e) { /* 保存できなくても続行 */ }
  }
  function loadOp() {
    try { return JSON.parse(localStorage.getItem(LS_OP) || 'null'); } catch (e) { return null; }
  }
  // 前回の操作があれば、完了と判定された場合も含めて再開ボタンを出す
  // (終了判定が早すぎて実際には残っていることがあるため)。消すのは「破棄」を押したときだけ。
  // 実行中のままページが閉じられた(=再読み込み等)場合は「途中で止まった」とみなす
  function showResume() {
    const op = loadOp();
    if (!op || op.status === 'discarded' || typeof op.target !== 'boolean' || state.bulk) {
      $resumeBox.style.display = 'none';
      return;
    }
    const when = new Date(op.t).toLocaleString();
    const name = op.target ? '全件共有ON' : '全件共有OFF';
    panel.querySelector('.resume-msg').textContent =
      (op.status === 'done'
        ? `前回の「${name}」は完了と判定されました(${when})。まだ残っている場合は続きから再開できます`
        : `前回の「${name}」が途中で止まっています(${when})`) +
      (!op.target && op.keep && op.keep.length ? `。残すタイトル ${op.keep.length} 語も復元します` : '');
    $resumeBox.style.display = '';
  }
  function resume() {
    const op = loadOp();
    if (!op || state.bulk || state.running) return;
    if (!op.target && op.keep) { $keep.value = op.keep.join('\n'); saveKeep(); }
    setAll(op.target, { resume: true });
  }
  function saveKeep() {
    try { localStorage.setItem(LS_KEEP, $keep.value); } catch (e) { /* 無視 */ }
  }

  // 誤操作防止: 1回目の押下で確認表示、5秒以内にもう一度押すと実行
  const armed = { on: 0, off: 0 };
  function armOrRun(target) {
    const k = target ? 'on' : 'off';
    const btn = target ? $allOn : $allOff;
    if (Date.now() - armed[k] < 5000) { armed[k] = 0; setAll(target); return; }
    armed[k] = Date.now();
    btn.textContent = 'もう一度押すと実行';
    const kw = keepWords().length;
    setStatus(`${ALL_LABEL[k]}: リストを先頭から最後までスクロールしながら、すべての項目を` +
      `${target ? '共有ON' : '共有OFF'}にします。` +
      (!target && kw ? `\n「共有のまま残すタイトル」(${kw}語)に一致する項目は変更しません。` : '') +
      '\n実行するには5秒以内にもう一度押してください。');
    setTimeout(() => { if (armed[k] && !state.bulk) { armed[k] = 0; btn.textContent = ALL_LABEL[k]; } }, 5000);
  }

  // ---------- 1件テスト: 共有中の1件を押して、何が起きたかを詳しく表示する ----------
  async function test1() {
    if (state.bulk || state.running) return;
    scan();
    const sw = live.find((x) => { const c = cache.get(x); return c && c.on && x.isConnected; });
    if (!sw) { setStatus('画面内に共有中(ON)の項目が見つかりません。共有中の項目が見える位置までスクロールしてください。'); return; }
    const c = cache.get(sw);
    const before = `aria-checked=${sw.getAttribute('aria-checked')} checked=${sw.checked}`;
    const t0 = Date.now();
    state.bulk = true; state.bulkHref = location.href;
    const hit = realClick(sw);
    setStatus(`1件テスト中…「${c.info.title}」を押しました。5秒待ちます。`);
    await sleep(5000);
    state.bulk = false;
    const el = current(sw) || sw;
    const after = `aria-checked=${el.getAttribute('aria-checked')} checked=${el.checked}` +
      (el !== sw ? '(要素は作り直されました)' : '');
    const w = writesSince(t0);
    const msg = `1件テスト: ${c.info.title}\n押した要素: <${hit.tagName.toLowerCase()} class="${String(hit.className).slice(0, 40)}">\n` +
      `押す前: ${before}\n押した後: ${after}\n` +
      `保存通信: ${w.length} 件\n` + w.slice(0, 5).map((r) => `  ${r.status} ${r.method} ${r.url.slice(0, 90)}`).join('\n') +
      (location.href !== state.bulkHref ? '\n※ページ遷移が起きました' : '') +
      '\n→ この後ページを再読み込みし、この本が本当にOFFになっているか確認してください。';
    console.log('[akids] ' + msg, { hit, before: sw, after: el, net: w });
    scan();
    setStatus(msg);
  }

  // ---------- 診断 ----------
  function diag() {
    const sws = findSwitches();
    const outer = new Set(sws);
    const kinds = {};
    for (const sw of sws) {
      const k = sw.matches('input[type="checkbox"]') ? 'input:checkbox'
        : sw.getAttribute('role') === 'switch' ? 'role=switch'
        : sw.hasAttribute('aria-checked') ? 'aria-checked' : 'aria-pressed';
      kinds[k] = (kinds[k] || 0) + 1;
    }
    const samples = sws.slice(0, 5).map((sw) => {
      const row = rowOfSlow(sw, outer).row;
      const i = infoOf(row, sw);
      return `${isOn(sw) ? 'ON ' : 'OFF'} | ${i.title} | 行=<${row.tagName.toLowerCase()} class="${(row.className || '').toString().slice(0, 40)}">`;
    });
    const sc = findScroller();
    const m = model || learn(sws);
    const excluded = document.querySelectorAll(SWITCH_SEL).length - sws.length;
    const msg = `トグル候補: ${sws.length} 個 ${JSON.stringify(kinds)}(ナビ等で除外 ${excluded} 個)\n` +
      `行構造: ${m ? `種類=${m.type} 深さ=${m.depth} 親=${m.parentSig.slice(0, 60)}` : '未判定'}\n` +
      `スクロール対象: <${sc.tagName.toLowerCase()} id="${sc.id}">\n` + samples.join('\n');
    console.log('[akids] 診断\n' + msg, sws.slice(0, 5));
    setStatus(msg);
  }

  // ---------- コピー ----------
  async function copy() {
    const tsv = ['タイトル\t補足\t画像URL',
      ...[...state.found.values()].map((i) => [i.title, i.sub, i.img].join('\t'))].join('\n');
    try {
      await navigator.clipboard.writeText(tsv);
      setStatus('クリップボードにコピーしました。');
    } catch (e) {
      const ta = document.createElement('textarea');
      ta.value = tsv;
      ta.style.cssText = 'width:100%;height:120px';
      panel.querySelector('.body').appendChild(ta);
      ta.select();
      setStatus('自動コピーできなかったので、下の欄から手動でコピーしてください。');
    }
  }

  // ---------- イベント ----------
  panel.addEventListener('click', (e) => {
    const a = e.target.closest('[data-a]');
    if (!a) return;
    e.preventDefault();
    switch (a.dataset.a) {
      case 'auto':
        if (state.bulk) break;
        state.pending = null; $bulk.disabled = true; $bulk.textContent = '共有解除を実行';
        state.running ? (state.running = false) : autoScroll(); break;
      case 'scan': setStatus(`トグル候補 ${scan()} 個をスキャンしました。`); break;
      case 'copy': copy(); break;
      case 'clear':
        state.found.clear(); state.seen.clear(); items.clear(); $list.textContent = '';
        live = []; model = null;  // WeakMap/WeakSetは参照が切れれば自動で解放される
        cache = new WeakMap(); rejected = new WeakSet(); scan(); break;
      case 'diag': diag(); break;
      case 'test1': test1(); break;
      case 'resume': resume(); break;
      case 'discard':
        saveOp({ status: 'discarded', t: Date.now() }); showResume(); break;
      case 'preview': if (!state.bulk && !state.running) preview(); break;
      case 'bulk': state.bulk ? (state.bulk = false) : (!state.running && bulkOff()); break;
      case 'allOn':
      case 'allOff':
        if (state.bulk) { state.bulk = false; break; }   // 実行中は「停止」として働く
        if (!state.running) armOrRun(a.dataset.a === 'allOn');
        break;
      case 'min': panel.classList.toggle('min'); break;
      case 'close': panel.style.display = 'none'; break;
    }
  });
  try { $keep.value = localStorage.getItem(LS_KEEP) || ''; } catch (e) { /* 無視 */ }
  $keep.addEventListener('input', () => {
    saveKeep();
    if (state.bulk) return;
    state.pending = null; $bulk.disabled = true; $bulk.textContent = '共有解除を実行';
  });
  panel.addEventListener('change', (e) => {
    const n = e.target.dataset.n;
    if (n) {
      const v = Number(e.target.value);
      if (Number.isFinite(v) && v >= 5) state[n] = v; else e.target.value = state[n];
      return;
    }
    const o = e.target.dataset.o;
    if (!o) return;
    state[o] = e.target.checked;
    reapply();
  });

  // パネルのドラッグ移動
  (() => {
    const h = panel.querySelector('header');
    let sx, sy, ox, oy;
    h.addEventListener('mousedown', (e) => {
      if (e.target.closest('a')) return;
      const r = panel.getBoundingClientRect();
      sx = e.clientX; sy = e.clientY; ox = r.left; oy = r.top;
      const mv = (ev) => {
        panel.style.left = ox + ev.clientX - sx + 'px';
        panel.style.top = oy + ev.clientY - sy + 'px';
        panel.style.right = panel.style.bottom = 'auto';
      };
      const up = () => { removeEventListener('mousemove', mv); removeEventListener('mouseup', up); };
      addEventListener('mousemove', mv); addEventListener('mouseup', up);
    });
  })();

  window.__akidsSharedList = { scan, diag, state, show: () => { panel.style.display = ''; } };
  setStatus('「全件読み込み開始」を押すと最後までスクロールしながら共有中の項目を集めます。');
  showResume();
})();
