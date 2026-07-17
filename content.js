/*
 * J-PlatPat 2列表示 (content script)
 *
 * J-PlatPat の文献表示画面(テキスト表示)で、
 *  - 「請求の範囲」と「詳細な説明」を左右2列に並べ、個別スクロール化
 *  - 図面ペインを固定幅+画面追従(sticky)にして常に表示
 *  - 文献を移動しても各ペインのスクロール位置を復元(位置記憶)
 *  - キーワードハイライトの位置をペイン右端にマーカー表示(クリックでジャンプ)
 *
 * J-PlatPat は Angular 製の SPA で、要素のクラス名が変わる可能性があるため、
 * パネルの「見出しテキスト」を手がかりにパネルを検出する方式にしています。
 */
(() => {
  'use strict';

  const LOG_PREFIX = '[JPP2col]';
  const log = (...args) => console.log(LOG_PREFIX, ...args);

  // J-PlatPat 文献表示のパネル見出し(検出対象)
  const ALL_TITLES = [
    '書誌', '要約', '請求の範囲', '詳細な説明', '図面',
    'ライセンス情報', '検索キー', '審査官フリーワード'
  ];
  const LEFT_TITLE = '請求の範囲';
  const RIGHT_TITLE = '詳細な説明';
  const DRAWING_TITLE = '図面';

  const CLS = {
    grid: 'jpp2-grid',
    col: 'jpp2-col',
    left: 'jpp2-left',
    right: 'jpp2-right',
    full: 'jpp2-full',
    sticky: 'jpp2-sticky-header',
    split: 'jpp2-split',
    textArea: 'jpp2-text-area',
    drawArea: 'jpp2-draw-area',
    wide: 'jpp2-wide',
    bib: 'jpp2-bib',
    abs: 'jpp2-abs',
    headZone: 'jpp2-head-zone',
    hMain: 'jpp2-h-main',
    hSelector: 'jpp2-h-selector',
    pager: 'jpp2-pager',
    enabledRoot: 'jpp2-enabled'
  };

  // 図面ペインの幅はピクセル固定
  const DRAW_W_DEFAULT = 600; // px
  const DRAW_W_MIN = 240;
  const DRAW_W_MAX = 1000;
  const DRAW_W_STEP = 40;

  let enabled = true;
  let drawWidth = DRAW_W_DEFAULT;
  let posMemory = true;          // 位置記憶 ON/OFF
  let ctrlOpen = false;          // 操作パネルの開閉状態
  let ctrlPos = null;            // 操作パネルの位置 {right, bottom} (ドラッグで変更可)
  let keywords = '';             // ハイライト語(空白区切り)
  let applyTimer = null;
  let observerRef = null;

  // ハイライトの色(複数語を色分け)
  const HL_COLORS = [
    '#ffff66', '#ffb366', '#99e699', '#99ccff',
    '#ff99cc', '#e0b3ff', '#ffe066', '#b3e6e6'
  ];

  // スクロール位置記憶(タブ内のみ・文献間で引き継ぐ)
  let savedScroll = null;        // { page, left, right }
  let freezeSave = false;        // 文献移動中は保存を一時停止

  // 現在適用中の列要素
  let leftColEl = null;
  let rightColEl = null;

  /* ---------- ユーティリティ ---------- */

  function findTitleEls(title, root) {
    const scope = root || document;
    const candidates = scope.querySelectorAll('span,div,h1,h2,h3,h4,p,label,b,strong,a');
    const hits = [];
    for (const el of candidates) {
      if (el.children.length > 2) continue;
      const t = (el.textContent || '').replace(/\s+/g, '');
      if (t === title) hits.push(el);
    }
    return hits; // 文書順(親→子)
  }

  function deepestTitleEl(title, root) {
    const hits = findTitleEls(title, root);
    if (!hits.length) return null;
    const visible = hits.filter(el => el.offsetParent !== null || el.getClientRects().length > 0);
    const list = visible.length ? visible : hits;
    return list[list.length - 1];
  }

  function countDistinctTitles(el) {
    let n = 0;
    for (const t of ALL_TITLES) {
      if (findTitleEls(t, el).length > 0) n++;
    }
    return n;
  }

  function panelRootOf(titleEl) {
    let node = titleEl;
    while (node.parentElement && node.parentElement !== document.body) {
      const parent = node.parentElement;
      if (countDistinctTitles(parent) > 1) break;
      node = parent;
    }
    return node;
  }

  function commonAncestor(a, b) {
    const seen = new Set();
    for (let n = a; n; n = n.parentElement) seen.add(n);
    for (let n = b; n; n = n.parentElement) {
      if (seen.has(n)) return n;
    }
    return null;
  }

  function childContaining(ancestor, node) {
    for (let n = node; n; n = n.parentElement) {
      if (n.parentElement === ancestor) return n;
    }
    return null;
  }

  // 指定文字列を含む最小の要素を探す(ヘッダー圧縮のアンカー検出用)
  function findElContaining(substr) {
    const candidates = document.querySelectorAll('span,div,p,label,a,button,h1,h2,h3,legend');
    let best = null;
    for (const el of candidates) {
      const t = (el.textContent || '').replace(/\s+/g, '');
      if (!t.includes(substr)) continue;
      if (el.offsetParent === null && el.getClientRects().length === 0) continue;
      if (!best || t.length < (best.textContent || '').replace(/\s+/g, '').length ||
          (t.length === (best.textContent || '').replace(/\s+/g, '').length && best.contains(el))) {
        best = el;
      }
    }
    return best;
  }

  function stickyHeaderOf(titleEl, panelRoot) {
    let best = null;
    for (let n = titleEl; n && n !== panelRoot; n = n.parentElement) {
      const h = n.getBoundingClientRect().height;
      if (h > 0 && h <= 80) best = n;
      else if (h > 80) break;
    }
    return best;
  }

  function throttle(fn, ms) {
    let last = 0, timer = null;
    return (...args) => {
      const now = Date.now();
      if (now - last >= ms) { last = now; fn(...args); }
      else if (!timer) {
        timer = setTimeout(() => { timer = null; last = Date.now(); fn(...args); }, ms - (now - last));
      }
    };
  }

  /* ---------- レイアウト適用 ---------- */

  function applyLayout() {
    if (!enabled) return;

    const leftTitleEl = deepestTitleEl(LEFT_TITLE);
    const rightTitleEl = deepestTitleEl(RIGHT_TITLE);
    if (!leftTitleEl || !rightTitleEl) {
      log('パネル見出しが見つかりません(この画面は対象外か、まだ描画中です)');
      updateButtons();
      return;
    }

    const leftRoot = panelRootOf(leftTitleEl);
    const rightRoot = panelRootOf(rightTitleEl);
    const container = commonAncestor(leftRoot, rightRoot);
    if (!container || container === document.body) {
      log('共通の親要素が特定できませんでした');
      return;
    }

    const leftItem = childContaining(container, leftRoot);
    const rightItem = childContaining(container, rightRoot);
    if (!leftItem || !rightItem || leftItem === rightItem) {
      log('2列化する列要素が特定できませんでした');
      return;
    }

    const alreadyApplied =
      container.classList.contains(CLS.grid) &&
      leftItem.classList.contains(CLS.left) &&
      rightItem.classList.contains(CLS.right);

    if (!alreadyApplied) {
      container.classList.add(CLS.grid);
      for (const child of container.children) {
        child.classList.remove(CLS.left, CLS.right, CLS.col, CLS.full);
        if (child === leftItem) child.classList.add(CLS.col, CLS.left);
        else if (child === rightItem) child.classList.add(CLS.col, CLS.right);
        else child.classList.add(CLS.full);
      }
      const leftHeader = stickyHeaderOf(leftTitleEl, leftItem);
      const rightHeader = stickyHeaderOf(rightTitleEl, rightItem);
      if (leftHeader) leftHeader.classList.add(CLS.sticky);
      if (rightHeader) rightHeader.classList.add(CLS.sticky);

      // 書誌と要約が両方あるときは、同じ行に横並びに配置して高さを節約する
      const panelItemOf = (title) => {
        const els = findTitleEls(title, container)
          .filter(el => el.offsetParent !== null || el.getClientRects().length > 0);
        if (!els.length) return null;
        return childContaining(container, panelRootOf(els[els.length - 1]));
      };
      const bibItem = panelItemOf('書誌');
      const absItem = panelItemOf('要約');
      if (bibItem && absItem && bibItem !== absItem &&
          bibItem !== leftItem && bibItem !== rightItem &&
          absItem !== leftItem && absItem !== rightItem) {
        bibItem.classList.remove(CLS.full);
        absItem.classList.remove(CLS.full);
        bibItem.classList.add(CLS.col, CLS.bib);
        absItem.classList.add(CLS.col, CLS.abs);
      }
    }

    // 図面パネル(テキスト領域の外にあるもの)を探す
    let drawRoot = null;
    for (const cand of findTitleEls(DRAWING_TITLE)) {
      if (cand.offsetParent === null && cand.getClientRects().length === 0) continue;
      const root = panelRootOf(cand);
      if (root && !container.contains(root) && !root.contains(container)) {
        drawRoot = root;
        break;
      }
    }
    if (drawRoot) {
      drawRoot.classList.add(CLS.col);
      const splitParent = commonAncestor(container, drawRoot);
      if (splitParent && splitParent !== document.body) {
        const textItem = childContaining(splitParent, container);
        const drawItem = childContaining(splitParent, drawRoot);
        if (textItem && drawItem && textItem !== drawItem) {
          splitParent.classList.add(CLS.split);
          textItem.classList.add(CLS.textArea);
          drawItem.classList.add(CLS.drawArea);
        }
        // ページ中央寄せの左右余白を潰す
        for (let n = splitParent; n && n !== document.body && n !== document.documentElement; n = n.parentElement) {
          n.classList.add(CLS.wide);
        }
      }
    }

    compactHeader();
    ensureNavButtons();
    ensureImgControls();
    applyDrawWidth();
    document.documentElement.classList.add(CLS.enabledRoot);

    leftColEl = leftItem;
    rightColEl = rightItem;
    attachScrollSave(leftItem, 'left');
    attachScrollSave(rightItem, 'right');

    if (!alreadyApplied) {
      log('2列表示を適用しました', { container, leftItem, rightItem });
      restoreScroll();     // 位置記憶の復元(文献移動後の再適用時)
      scheduleRefresh();   // ハイライトとマーカーの再計算
    }
    positionOverlays();
    updateButtons();
  }

  // 文献ヘッダー領域(番号・ステータス/表示形式/ボタン列)を1行のコンパクトな帯に再配置する。
  // J-PlatPat実DOMのID(#result_header, #result_selector等)に基づく確実な方式。
  let headerStatus = '';
  function logHeaderStatus(msg, extra) {
    if (headerStatus === msg) return; // 同じ状態の重複ログを防ぐ
    headerStatus = msg;
    log('ヘッダー圧縮: ' + msg, extra || '');
  }

  let rsHome = null; // #result_selector の元の位置(OFF時の復元用)

  function headerNeedsWork() {
    const rh = document.getElementById('result_header');
    const rs = document.getElementById('result_selector');
    if (!rh || !rs) return false; // この画面には対象がない
    const hd = rh.querySelector('.headerDetail') || rh;
    if (rs.parentElement !== hd) return true;
    const title = hd.querySelector('.headerDetail__title');
    if (title && title.querySelector('br')) return true;
    return !hd.classList.contains(CLS.headZone);
  }

  function compactHeader() {
    const rh = document.getElementById('result_header');
    const rs = document.getElementById('result_selector');
    if (!rh || !rs) {
      logHeaderStatus('対象要素なし (#result_header=' + !!rh + ', #result_selector=' + !!rs + ')');
      return;
    }
    const hd = rh.querySelector('.headerDetail') || rh;
    const title = hd.querySelector('.headerDetail__title');
    const buttons = hd.querySelector('.headerDetail__buttons');

    // 番号・ステータスの改行(<br>)を全角スペースに置き換えて1行化
    if (title) {
      title.querySelectorAll('br').forEach(br => br.replaceWith(document.createTextNode('　')));
    }

    // 表示形式・一次文献のブロックを、番号とボタン列の間に移動して1行に配置
    if (rs.parentElement !== hd) {
      rsHome = { parent: rs.parentElement, next: rs.nextSibling };
      if (buttons) hd.insertBefore(rs, buttons);
      else hd.appendChild(rs);
    }

    hd.classList.add(CLS.headZone);
    rh.classList.add(CLS.hMain);
    rs.classList.add(CLS.hSelector);

    // ページャ行(前の文献/次の文献)の余白も圧縮
    ['upPagerArea', 'underPagerArea'].forEach((id) => {
      const el = document.getElementById(id);
      if (el) el.classList.add(CLS.pager);
    });

    flushObserver();
    logHeaderStatus('適用しました', hd);
  }

  /* ---------- 図面のその場拡大・縮小・回転 ----------
   * ペイン内に表示済みの画像をCSS transformで変形するだけなので、
   * サーバーへの追加リクエストは一切発生しない。 */

  const IMG_SCALE_STEP = 1.25;
  const IMG_SCALE_MIN = 0.25;
  const IMG_SCALE_MAX = 8;

  function imgCtlNeedsWork() {
    return !!document.getElementById('lnkEnlargeAndSpin') && !document.getElementById('jpp2-imgctl');
  }

  function currentDrawImage() {
    const link = document.getElementById('lnkEnlargeAndSpin');
    if (!link) return null;
    const scope = link.closest('.l-toggle') || document;
    return scope.querySelector('img.main_image') ||
           scope.querySelector('.l-toggle__content__fig img') ||
           document.querySelector('img.main_image');
  }

  function getImgState(img) {
    return {
      s: parseFloat(img.dataset.jpp2S || '1'),
      r: parseInt(img.dataset.jpp2R || '0', 10),
      tx: parseFloat(img.dataset.jpp2Tx || '0'),
      ty: parseFloat(img.dataset.jpp2Ty || '0')
    };
  }

  function setImgState(img, st) {
    img.dataset.jpp2S = String(st.s);
    img.dataset.jpp2R = String(st.r);
    img.dataset.jpp2Tx = String(st.tx);
    img.dataset.jpp2Ty = String(st.ty);
    const transformed = st.s !== 1 || st.r !== 0 || st.tx !== 0 || st.ty !== 0;
    img.style.transform = transformed
      ? 'translate(' + st.tx + 'px, ' + st.ty + 'px) scale(' + st.s + ') rotate(' + st.r + 'deg)'
      : '';
    img.style.transformOrigin = 'center center';
    img.classList.toggle('jpp2-img-transformed', transformed);
    if (img.parentElement) img.parentElement.classList.toggle('jpp2-img-clip', transformed);
  }

  function adjustImg(fn) {
    const img = currentDrawImage();
    if (!img) return;
    const st = getImgState(img);
    fn(st);
    st.s = Math.min(IMG_SCALE_MAX, Math.max(IMG_SCALE_MIN, st.s));
    st.r = ((st.r % 360) + 360) % 360;
    setImgState(img, st);
  }

  function ensureImgControls() {
    if (!imgCtlNeedsWork()) return;
    const link = document.getElementById('lnkEnlargeAndSpin');
    const holder = link.parentElement;
    if (!holder) return;

    const grp = document.createElement('span');
    grp.id = 'jpp2-imgctl';
    // 文字グリフはOSのフォント代替で高さがずれるため、すべてSVGアイコンで描く
    // 並び・アイコンは公式の「拡大および回転」ウィンドウに合わせる(拡大→縮小→右回転→左回転)
    const ICONS = {
      zoomIn: '<svg viewBox="0 0 24 24"><path d="M15.5 14h-.79l-.28-.27A6.47 6.47 0 0 0 16 9.5 6.5 6.5 0 1 0 9.5 16c1.61 0 3.09-.59 4.23-1.57l.27.28v.79l5 4.99L20.49 19l-4.99-5zm-6 0C7.01 14 5 11.99 5 9.5S7.01 5 9.5 5 14 7.01 14 9.5 11.99 14 9.5 14z"/><path d="M10 7H9v2H7v1h2v2h1v-2h2V9h-2z"/></svg>',
      zoomOut: '<svg viewBox="0 0 24 24"><path d="M15.5 14h-.79l-.28-.27A6.47 6.47 0 0 0 16 9.5 6.5 6.5 0 1 0 9.5 16c1.61 0 3.09-.59 4.23-1.57l.27.28v.79l5 4.99L20.49 19l-4.99-5zm-6 0C7.01 14 5 11.99 5 9.5S7.01 5 9.5 5 14 7.01 14 9.5 11.99 14 9.5 14z"/><path d="M7 9h5v1H7z"/></svg>',
      rotL: '<svg viewBox="0 0 24 24"><path d="M12 5V1L7 6l5 5V7c3.31 0 6 2.69 6 6s-2.69 6-6 6-6-2.69-6-6H4c0 4.42 3.58 8 8 8s8-3.58 8-8-3.58-8-8-8z"/></svg>',
      rotR: '<svg viewBox="0 0 24 24"><path d="M12 5V1l5 5-5 5V7c-3.31 0-6 2.69-6 6s2.69 6 6 6 6-2.69 6-6h2c0 4.42-3.58 8-8 8s-8-3.58-8-8 3.58-8 8-8z"/></svg>',
      reset: '<svg viewBox="0 0 24 24"><path d="M12 4a8 8 0 1 1-8 8h2a6 6 0 1 0 6-6v3L7 5l5-4v3z"/><rect x="9" y="9" width="6" height="6" rx="1"/></svg>'
    };
    const mk = (icon, title, fn) => {
      const b = document.createElement('button');
      b.type = 'button';
      b.innerHTML = ICONS[icon];
      b.title = title;
      b.addEventListener('click', (e) => { e.preventDefault(); e.stopPropagation(); fn(); });
      grp.appendChild(b);
    };
    mk('zoomIn', '拡大(その場・通信なし)', () => adjustImg(st => { st.s *= IMG_SCALE_STEP; }));
    mk('zoomOut', '縮小(その場・通信なし)', () => adjustImg(st => { st.s /= IMG_SCALE_STEP; }));
    mk('rotR', '右に90°回転', () => adjustImg(st => { st.r += 90; }));
    mk('rotL', '左に90°回転', () => adjustImg(st => { st.r -= 90; }));
    mk('reset', '元のサイズ・向きに戻す', () => adjustImg(st => { st.s = 1; st.r = 0; st.tx = 0; st.ty = 0; }));
    holder.appendChild(grp);
    flushObserver();
    log('図面操作ボタンを追加しました');
  }

  // 変形中の画像はドラッグで表示位置を移動できるようにする
  let panState = null;
  function initImagePan() {
    document.addEventListener('pointerdown', (e) => {
      if (!enabled) return;
      const img = e.target;
      if (!(img instanceof HTMLImageElement) || !img.classList.contains('jpp2-img-transformed')) return;
      e.preventDefault();
      const st = getImgState(img);
      panState = { img, startX: e.clientX, startY: e.clientY, tx: st.tx, ty: st.ty };
    }, true);
    document.addEventListener('pointermove', (e) => {
      if (!panState) return;
      const st = getImgState(panState.img);
      st.tx = panState.tx + (e.clientX - panState.startX);
      st.ty = panState.ty + (e.clientY - panState.startY);
      setImgState(panState.img, st);
    }, true);
    document.addEventListener('pointerup', () => { panState = null; }, true);
  }

  function removeImgControls() {
    const grp = document.getElementById('jpp2-imgctl');
    if (grp) grp.remove();
    document.querySelectorAll('img[data-jpp2-s]').forEach((img) => {
      img.style.transform = '';
      img.classList.remove('jpp2-img-transformed');
      delete img.dataset.jpp2S; delete img.dataset.jpp2R;
      delete img.dataset.jpp2Tx; delete img.dataset.jpp2Ty;
      if (img.parentElement) img.parentElement.classList.remove('jpp2-img-clip');
    });
  }

  /* ---------- 前の文献/次の文献ボタン ----------
   * ヘッダーのボタン群の左に←/→を追加。クリックはページ内の
   * 既存の「前の文献/次の文献」への転送のみで、通信は利用者が
   * 元のページャを操作した場合と完全に同一。 */

  function navNeedsWork() {
    const rh = document.getElementById('result_header');
    if (!rh) return false;
    const buttons = rh.querySelector('.headerDetail__buttons');
    if (!buttons) return false;
    return !buttons.querySelector('#jpp2-nav');
  }

  function clickNativePager(which) {
    const scope = document.getElementById('upPagerArea') || document;
    const el = scope.querySelector(which === 'prev' ? '[id$="lblPrev"]' : '[id$="lblNext"]');
    if (el) el.click();
  }

  function ensureNavButtons() {
    if (!navNeedsWork()) return;
    const buttons = document.querySelector('#result_header .headerDetail__buttons');
    const wrap = document.createElement('span');
    wrap.id = 'jpp2-nav';
    const mk = (dir, title, path) => {
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'jpp2-nav-btn';
      b.title = title;
      b.innerHTML = '<svg viewBox="0 0 24 24"><path d="' + path + '"/></svg>';
      b.addEventListener('click', (e) => {
        e.preventDefault();
        e.stopPropagation();
        clickNativePager(dir);
      });
      wrap.appendChild(b);
    };
    mk('prev', '前の文献', 'M15.41 7.41 14 6l-6 6 6 6 1.41-1.41L10.83 12z');
    mk('next', '次の文献', 'M8.59 16.59 13.17 12 8.59 7.41 10 6l6 6-6 6z');
    buttons.appendChild(wrap); // ボタン群の右端(URLの右)に配置
    // 高さは隣の既存ボタンの実測に合わせる
    const ref = buttons.querySelector('a.mdc-button, a[id^="docuTitleArea_btn"]');
    if (ref) {
      const h = Math.round(ref.getBoundingClientRect().height);
      if (h > 16) wrap.querySelectorAll('button').forEach(b => { b.style.setProperty('height', h + 'px', 'important'); });
    }
    flushObserver();
    log('前後移動ボタンを追加しました');
  }

  function removeNavButtons() {
    const el = document.getElementById('jpp2-nav');
    if (el) el.remove();
  }

  function restoreHeader() {
    const rs = document.getElementById('result_selector');
    if (rs && rsHome && rsHome.parent && rsHome.parent.isConnected) {
      rsHome.parent.insertBefore(rs, rsHome.next && rsHome.next.isConnected ? rsHome.next : null);
    }
    rsHome = null;
  }

  function removeLayout() {
    document.documentElement.classList.remove(CLS.enabledRoot);
    restoreHeader();
    removeNavButtons();
    removeImgControls();
    for (const cls of [CLS.grid, CLS.col, CLS.left, CLS.right, CLS.full,
                       CLS.bib, CLS.abs,
                       CLS.sticky, CLS.split, CLS.textArea, CLS.drawArea, CLS.wide,
                       CLS.headZone, CLS.hMain, CLS.hSelector, CLS.pager]) {
      document.querySelectorAll('.' + cls).forEach(el => el.classList.remove(cls));
    }
    clearHighlights();
    flushObserver();
    hideOverlays();
    log('2列表示を解除しました');
    updateButtons();
  }

  function applyDrawWidth() {
    document.documentElement.style.setProperty('--jpp2-draw-w', drawWidth + 'px');
  }

  function changeDrawWidth(delta) {
    drawWidth = Math.min(DRAW_W_MAX, Math.max(DRAW_W_MIN, drawWidth + delta));
    applyDrawWidth();
    saveState();
    updateButtons();
    positionOverlays();
  }

  function scheduleApply() {
    if (applyTimer) clearTimeout(applyTimer);
    applyTimer = setTimeout(() => {
      applyTimer = null;
      applyLayout();
    }, 500);
  }

  /* ---------- スクロール位置の記憶・復元 ---------- */

  function attachScrollSave(el, key) {
    if (el.dataset.jpp2ScrollKey === key) return;
    el.dataset.jpp2ScrollKey = key;
    el.addEventListener('scroll', throttle(() => {
      if (!posMemory || freezeSave || !enabled) return;
      savedScroll = savedScroll || {};
      savedScroll[key] = el.scrollTop;
    }, 200), { passive: true });
  }

  function restoreScroll() {
    if (!posMemory || !savedScroll) { freezeSave = false; return; }
    const target = Object.assign({}, savedScroll);
    const attempts = [80, 400, 1200, 2500];
    attempts.forEach((delay, i) => {
      setTimeout(() => {
        if (!enabled) { freezeSave = false; return; }
        if (typeof target.page === 'number') window.scrollTo(0, target.page);
        if (leftColEl && typeof target.left === 'number') leftColEl.scrollTop = target.left;
        if (rightColEl && typeof target.right === 'number') rightColEl.scrollTop = target.right;
        if (i === attempts.length - 1) {
          freezeSave = false;
          savedScroll = Object.assign({}, target); // 復元後の値を正とする
          positionOverlays();
        }
      }, delay);
    });
    log('スクロール位置を復元します', target);
  }

  /* ---------- キーワードハイライト ----------
   * ブラウザのCtrl+F(ページ内検索)のハイライトはブラウザ内部の描画で
   * HTMLには存在しないため、拡張からは検出できない。
   * 代わりに拡張自身でハイライトを行う。 */

  function flushObserver() {
    if (observerRef) observerRef.takeRecords(); // 自分のDOM変更で再適用ループしないよう捨てる
  }

  function clearHighlights() {
    document.querySelectorAll('span.jpp2-hl').forEach(sp => {
      const parent = sp.parentNode;
      if (!parent) return;
      parent.replaceChild(document.createTextNode(sp.textContent), sp);
      parent.normalize();
    });
  }

  function highlightWord(root, word, color) {
    const wordLower = word.toLowerCase();
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
      acceptNode(n) {
        if (!n.nodeValue || n.nodeValue.toLowerCase().indexOf(wordLower) === -1) {
          return NodeFilter.FILTER_REJECT;
        }
        const p = n.parentElement;
        if (!p || p.closest('.jpp2-hl,#jpp2-controls,script,style,textarea,input')) {
          return NodeFilter.FILTER_REJECT;
        }
        return NodeFilter.FILTER_ACCEPT;
      }
    });
    const nodes = [];
    while (walker.nextNode()) nodes.push(walker.currentNode);
    let count = 0;
    for (const node of nodes) {
      let n = node;
      while (n) {
        const idx = n.nodeValue.toLowerCase().indexOf(wordLower);
        if (idx === -1) break;
        const match = n.splitText(idx);
        const rest = match.splitText(word.length);
        const span = document.createElement('span');
        span.className = 'jpp2-hl';
        span.style.backgroundColor = color;
        match.parentNode.replaceChild(span, match);
        span.appendChild(match);
        n = rest;
        count++;
      }
    }
    return count;
  }

  function highlightAll() {
    if (!enabled) return;
    clearHighlights();
    const words = keywords.split(/[\s　]+/).filter(Boolean).slice(0, HL_COLORS.length);
    const cols = [leftColEl, rightColEl].filter(c => c && c.isConnected);
    if (words.length && cols.length) {
      let total = 0;
      for (const col of cols) {
        words.forEach((w, i) => { total += highlightWord(col, w, HL_COLORS[i % HL_COLORS.length]); });
      }
      log('ハイライト: ' + words.join(', ') + ' (' + total + '件)');
    }
    flushObserver();
    recomputeMarkers();
  }

  /* ---------- ハイライトのスクロールバーマーカー ---------- */

  let overlayLeft = null;
  let overlayRight = null;

  function ensureOverlays() {
    if (!overlayLeft || !document.body.contains(overlayLeft)) {
      overlayLeft = document.createElement('div');
      overlayLeft.className = 'jpp2-markers';
      document.body.appendChild(overlayLeft);
    }
    if (!overlayRight || !document.body.contains(overlayRight)) {
      overlayRight = document.createElement('div');
      overlayRight.className = 'jpp2-markers';
      document.body.appendChild(overlayRight);
    }
  }

  function parseColor(str) {
    const m = /rgba?\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)(?:\s*,\s*([\d.]+))?\)/.exec(str || '');
    if (!m) return null;
    return [Number(m[1]), Number(m[2]), Number(m[3]), m[4] === undefined ? 1 : Number(m[4])];
  }

  // ハイライト(色付き背景の短いテキスト)を検出
  function computeHits(col) {
    const hits = [];
    if (!col || !col.isConnected) return hits;
    // インラインstyle指定・ハイライト系クラスを優先的に、なければ広く走査
    let candidates = col.querySelectorAll('[style*="background"],mark,[class*="high" i],[class*="key" i]');
    if (!candidates.length) candidates = col.querySelectorAll('span,em,font,b');
    const colRect = col.getBoundingClientRect();
    let scanned = 0;
    for (const el of candidates) {
      if (++scanned > 20000) break;
      const txt = (el.textContent || '').trim();
      if (!txt || txt.length > 120) continue;
      let bg = el.style ? el.style.backgroundColor : '';
      if (!bg) bg = getComputedStyle(el).backgroundColor;
      const c = parseColor(bg);
      if (!c) continue;
      const [r, g, b, a] = c;
      if (a === 0) continue;
      if (r >= 240 && g >= 240 && b >= 240) continue;                 // 白
      if (Math.abs(r - g) < 12 && Math.abs(g - b) < 12) continue;     // グレー系
      const rect = el.getBoundingClientRect();
      if (rect.height === 0) continue;
      hits.push({
        top: rect.top - colRect.top + col.scrollTop,
        color: bg,
        text: txt
      });
    }
    return hits;
  }

  function renderMarkers(col, overlay) {
    if (!col || !col.isConnected) { overlay.style.display = 'none'; return; }
    const hits = computeHits(col);
    overlay.textContent = '';
    const total = Math.max(col.scrollHeight, 1);
    for (const hit of hits) {
      const mk = document.createElement('div');
      mk.className = 'jpp2-marker';
      mk.style.top = Math.min(99.5, (hit.top / total) * 100) + '%';
      mk.style.background = hit.color;
      mk.title = hit.text;
      mk.addEventListener('click', () => {
        col.scrollTo({ top: Math.max(0, hit.top - col.clientHeight / 3), behavior: 'smooth' });
      });
      overlay.appendChild(mk);
    }
  }

  function recomputeMarkers() {
    if (!enabled) { hideOverlays(); return; }
    ensureOverlays();
    renderMarkers(leftColEl, overlayLeft);
    renderMarkers(rightColEl, overlayRight);
    positionOverlays();
  }

  function positionOverlays() {
    if (!overlayLeft || !overlayRight) return;
    const place = (col, overlay) => {
      if (!enabled || !col || !col.isConnected) { overlay.style.display = 'none'; return; }
      const r = col.getBoundingClientRect();
      if (r.height < 50 || r.width < 50) { overlay.style.display = 'none'; return; }
      overlay.style.display = 'block';
      overlay.style.left = (r.right - 14) + 'px';
      overlay.style.top = r.top + 'px';
      overlay.style.height = r.height + 'px';
    };
    place(leftColEl, overlayLeft);
    place(rightColEl, overlayRight);
  }

  function hideOverlays() {
    if (overlayLeft) overlayLeft.style.display = 'none';
    if (overlayRight) overlayRight.style.display = 'none';
  }

  let refreshTimers = [];
  function scheduleRefresh() {
    refreshTimers.forEach(clearTimeout);
    refreshTimers = [800, 2500, 6000].map(d => setTimeout(highlightAll, d));
  }

  /* ---------- 操作ボタン ---------- */

  let controls = null;
  let toggleBtn = null;
  let posBtn = null;
  let narrowBtn = null;
  let widenBtn = null;
  let widthLabel = null;
  let hlInput = null;
  let applyKeywordsNow = null; // Enterで即時適用するための参照

  function ensureControls() {
    if (controls && document.body.contains(controls)) return;

    controls = document.createElement('div');
    controls.id = 'jpp2-controls';

    // ハイライト語の入力欄
    const hlGroup = document.createElement('div');
    hlGroup.className = 'jpp2-hl-group';

    hlInput = document.createElement('input');
    hlInput.type = 'text';
    hlInput.className = 'jpp2-hl-input';
    hlInput.placeholder = 'ハイライト語(空白区切り)';
    hlInput.title = '入力した語を両ペインでハイライトします(複数語は空白区切りで色分け・文献を移動しても維持)';
    hlInput.value = keywords;
    let hlTimer = null;
    const applyKeywords = () => {
      if (hlTimer) { clearTimeout(hlTimer); hlTimer = null; }
      keywords = hlInput.value;
      saveState();
      highlightAll();
    };
    applyKeywordsNow = applyKeywords;
    hlInput.addEventListener('input', () => {
      if (hlTimer) clearTimeout(hlTimer);
      hlTimer = setTimeout(applyKeywords, 600);
    });
    // ※キー操作(Enter等)は init() のwindowキャプチャ側で処理する。
    //   J-PlatPat は N(次の文献)/B(前の文献)等のショートカットを
    //   ページ側で監視しており、入力欄のキーが漏れると文献が移動してしまうため、
    //   入力欄フォーカス中のキーイベントは最上流(window・capture)で遮断する。

    const hlClear = document.createElement('button');
    hlClear.type = 'button';
    hlClear.className = 'jpp2-hl-clear';
    hlClear.textContent = '×';
    hlClear.title = 'ハイライトを消す';
    hlClear.addEventListener('click', () => {
      hlInput.value = '';
      keywords = '';
      saveState();
      highlightAll();
    });

    hlGroup.appendChild(hlInput);
    hlGroup.appendChild(hlClear);

    // 図面幅の調整
    const widthGroup = document.createElement('div');
    widthGroup.className = 'jpp2-width-group';

    narrowBtn = document.createElement('button');
    narrowBtn.type = 'button';
    narrowBtn.textContent = '図面 −';
    narrowBtn.title = '図面ペインを狭くする(テキストが広がります)';
    narrowBtn.addEventListener('click', () => changeDrawWidth(-DRAW_W_STEP));

    widthLabel = document.createElement('span');
    widthLabel.className = 'jpp2-width-label';

    widenBtn = document.createElement('button');
    widenBtn.type = 'button';
    widenBtn.textContent = '図面 +';
    widenBtn.title = '図面ペインを広くする';
    widenBtn.addEventListener('click', () => changeDrawWidth(DRAW_W_STEP));

    widthGroup.appendChild(narrowBtn);
    widthGroup.appendChild(widthLabel);
    widthGroup.appendChild(widenBtn);

    // 位置記憶 ON/OFF
    posBtn = document.createElement('button');
    posBtn.className = 'jpp2-pos-btn';
    posBtn.type = 'button';
    posBtn.title = '文献を移動しても各ペインのスクロール位置を引き継ぎます';
    posBtn.addEventListener('click', () => {
      posMemory = !posMemory;
      if (!posMemory) savedScroll = null;
      saveState();
      updateButtons();
    });

    // 2列表示 ON/OFF
    toggleBtn = document.createElement('button');
    toggleBtn.id = 'jpp2-toggle';
    toggleBtn.type = 'button';
    toggleBtn.addEventListener('click', () => {
      enabled = !enabled;
      saveState();
      if (enabled) { applyLayout(); scheduleRefresh(); }
      else removeLayout();
    });

    // 開閉ボタン
    const fabBtn = document.createElement('button');
    fabBtn.id = 'jpp2-fab';
    fabBtn.type = 'button';
    fabBtn.textContent = '≡';
    fabBtn.title = '2列表示ツールの設定を開閉';
    fabBtn.addEventListener('click', () => {
      ctrlOpen = !ctrlOpen;
      saveState();
      updateButtons();
    });

    // 常時表示の横一列: [ドラッグつまみ][ハイライト入力][≡]
    const mainRow = document.createElement('div');
    mainRow.id = 'jpp2-mainrow';

    const dragHandle = document.createElement('span');
    dragHandle.id = 'jpp2-drag';
    dragHandle.textContent = '⠿';
    dragHandle.title = 'ドラッグで移動(位置は記憶されます)';
    initCtrlDrag(dragHandle);

    mainRow.appendChild(dragHandle);
    mainRow.appendChild(hlGroup);
    mainRow.appendChild(fabBtn);

    controls.appendChild(widthGroup);
    controls.appendChild(posBtn);
    controls.appendChild(toggleBtn);
    controls.appendChild(mainRow);
    document.body.appendChild(controls);
    applyCtrlPos();

    // パネルの外をクリックしたら畳む
    document.addEventListener('click', (e) => {
      if (!ctrlOpen) return;
      if (e.target && e.target.closest && e.target.closest('#jpp2-controls')) return;
      ctrlOpen = false;
      saveState();
      updateButtons();
    }, true);

    updateButtons();
  }

  // 操作パネルの位置適用(未設定なら既定位置=CSSの値)
  function applyCtrlPos() {
    if (!controls) return;
    if (ctrlPos && typeof ctrlPos.right === 'number' && typeof ctrlPos.bottom === 'number') {
      const r = Math.min(Math.max(ctrlPos.right, 0), Math.max(0, window.innerWidth - 80));
      const b = Math.min(Math.max(ctrlPos.bottom, 0), Math.max(0, window.innerHeight - 50));
      controls.style.right = r + 'px';
      controls.style.bottom = b + 'px';
    }
  }

  // ドラッグつまみで操作パネルを移動
  function initCtrlDrag(handle) {
    let drag = null;
    handle.addEventListener('pointerdown', (e) => {
      e.preventDefault();
      const rect = controls.getBoundingClientRect();
      drag = {
        startX: e.clientX,
        startY: e.clientY,
        right: window.innerWidth - rect.right,
        bottom: window.innerHeight - rect.bottom
      };
      handle.setPointerCapture(e.pointerId);
    });
    handle.addEventListener('pointermove', (e) => {
      if (!drag) return;
      ctrlPos = {
        right: drag.right - (e.clientX - drag.startX),
        bottom: drag.bottom - (e.clientY - drag.startY)
      };
      applyCtrlPos();
    });
    handle.addEventListener('pointerup', (e) => {
      if (!drag) return;
      drag = null;
      handle.releasePointerCapture(e.pointerId);
      saveState();
    });
  }

  function updateButtons() {
    if (!controls) return;
    toggleBtn.textContent = enabled ? '2列表示:ON' : '2列表示:OFF';
    toggleBtn.classList.toggle('jpp2-on', enabled);
    posBtn.textContent = posMemory ? '位置記憶:ON' : '位置記憶:OFF';
    posBtn.classList.toggle('jpp2-on', posMemory);
    widthLabel.textContent = drawWidth + 'px';
    controls.classList.toggle('jpp2-disabled', !enabled);
    controls.classList.toggle('jpp2-collapsed', !ctrlOpen);
  }

  /* ---------- 状態の保存/復元 ---------- */

  function saveState() {
    try {
      chrome.storage.local.set({
        jpp2Enabled: enabled,
        jpp2DrawWidth: drawWidth,
        jpp2PosMemory: posMemory,
        jpp2CtrlOpen: ctrlOpen,
        jpp2CtrlPos: ctrlPos,
        jpp2Keywords: keywords
      });
    } catch (e) { /* noop */ }
  }

  function loadState(cb) {
    try {
      chrome.storage.local.get(
        { jpp2Enabled: true, jpp2DrawWidth: DRAW_W_DEFAULT, jpp2PosMemory: true, jpp2CtrlOpen: false, jpp2CtrlPos: null, jpp2Keywords: '' },
        (res) => {
          let w = Number(res.jpp2DrawWidth) || DRAW_W_DEFAULT;
          if (w <= 100) w = DRAW_W_DEFAULT; // 旧バージョン(%指定)の保存値はリセット
          cb(!!res.jpp2Enabled, w, !!res.jpp2PosMemory, !!res.jpp2CtrlOpen, res.jpp2CtrlPos || null, String(res.jpp2Keywords || ''));
        }
      );
    } catch (e) {
      cb(true, DRAW_W_DEFAULT, true, false, null, '');
    }
  }

  /* ---------- 起動 ---------- */

  function init() {
    loadState((state, width, posMem, open, pos, kw) => {
      enabled = state;
      drawWidth = width;
      posMemory = posMem;
      ctrlOpen = open;
      ctrlPos = pos;
      keywords = kw;
      ensureControls();
      ensureOverlays();
      if (enabled) scheduleApply();

      // ページスクロール位置の保存+マーカー位置の追従
      window.addEventListener('scroll', throttle(() => {
        if (enabled && posMemory && !freezeSave && document.querySelector('.' + CLS.left)) {
          savedScroll = savedScroll || {};
          savedScroll.page = window.scrollY;
        }
        positionOverlays();
      }, 100), { passive: true });
      window.addEventListener('resize', throttle(positionOverlays, 200));

      // 入力欄フォーカス中のキーイベントを遮断(J-PlatPatのN/B等のショートカット暴発防止)
      // window のキャプチャ段階(伝播の最上流)で止めるので、ページ側のリスナーには一切届かない。
      // 文字の入力自体はブラウザの既定動作なので、遮断しても問題なく入力できる。
      ['keydown', 'keypress', 'keyup'].forEach((type) => {
        window.addEventListener(type, (e) => {
          const t = e.target;
          if (!t || !t.closest || !t.closest('#jpp2-controls')) return;
          e.stopImmediatePropagation();
          e.stopPropagation();
          if (type === 'keydown' && t === hlInput && !e.isComposing) {
            if (e.key === 'Enter' && applyKeywordsNow) applyKeywordsNow();
            else if (e.key === 'Escape') hlInput.blur();
          }
        }, true);
      });

      // 「次の文献」「前の文献」等のクリックで、移動が完了するまで位置の上書き保存を止める
      document.addEventListener('click', (e) => {
        const t = e.target && e.target.closest ? e.target.closest('a,button') : null;
        if (!t || t.closest('#jpp2-controls')) return;
        const txt = (t.textContent || '').replace(/\s+/g, '');
        if (/次の文献|前の文献|^表示$/.test(txt)) {
          if (posMemory && savedScroll) freezeSave = true;
        }
      }, true);

      // SPAの再描画・画面遷移に追従する
      let markerDirtyTimer = null;
      const observer = new MutationObserver(() => {
        ensureControls();
        if (!enabled) return;
        if (!document.querySelector('.' + CLS.grid) ||
            !document.querySelector('.' + CLS.left) ||
            !document.querySelector('.' + CLS.right)) {
          scheduleApply();
        } else {
          // ヘッダー・図面操作ボタンが後から描画・再描画された場合の再試行
          if (headerNeedsWork()) {
            compactHeader();
          }
          if (navNeedsWork()) {
            ensureNavButtons();
          }
          if (imgCtlNeedsWork()) {
            ensureImgControls();
          }
          // ハイライトが後から描画される場合に備えてマーカーを更新
          if (markerDirtyTimer) clearTimeout(markerDirtyTimer);
          markerDirtyTimer = setTimeout(recomputeMarkers, 2000);
        }
      });
      initImagePan();
      observerRef = observer;
      observer.observe(document.body, { childList: true, subtree: true });
      log('初期化しました (enabled=' + enabled + ', drawWidth=' + drawWidth + 'px, posMemory=' + posMemory + ')');
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
