'use strict';
(() => {
  // 0. iframe 埋め込み防止（クリックジャッキング対策）
  if (window.self !== window.top) {
    const root = document.getElementById('appRoot');
    if (root) {
      root.replaceChildren();
      const warn = document.createElement('div');
      warn.className = 'frame-blocked';
      warn.textContent = 'セキュリティ保護のため、埋め込みフレーム（iframe）内での実行は停止されています。直接ページを開いてご利用ください。';
      root.appendChild(warn);
    }
    return;
  }

  // リソース上限（スマホのメモリ保護を考慮した上限設定）
  const MAX_FILE_BYTES = 40 * 1024 * 1024;          // 40MB
  const MAX_INPUT_PIXELS = 50_000_000;              // 5,000万画素（デコード前後に遮断）
  const MAX_DIMENSION = 32767;                      // 単辺の最大ピクセル数
  const MAX_SINGLE_OUTPUT_PIXELS = 16_000_000;      // 1枚あたり1,600万画素
  const MAX_TOTAL_OUTPUT_PIXELS = 45_000_000;       // 全枚数合計4,500万画素
  const MAX_ZIP_BYTES = 80 * 1024 * 1024;           // 80MB
  const MIN_SCALE_PCT = 20;

  const RATIOS = Object.freeze({
    '1:1': 1,
    '4:5': 4 / 5,
    '3:4': 3 / 4,
    '1.91:1': 1.91
  });

  // ユーザー向け日本語メッセージのみを透過させる専用エラークラス
  class UserFacingError extends Error {
    constructor(message) {
      super(message);
      this.name = 'UserFacingError';
    }
  }

  // =========================================================================
  // 1. コアロジック（純粋関数群：デコード前ヘッダ解析・枠計算・出力寸法・ZIP生成/検証）
  // =========================================================================

  /**
   * デコード前にバイナリから画像形式と寸法(width, height)を厳密に読み取る
   * 返り値:
   *  - { status: 'ok', mime, width, height } : 解析成功
   *  - { status: 'need_more' }               : JPEGでバッファ末尾によりSOF未到達（追加読み込みが必要）
   *  - { status: 'invalid' }                 : 非対応形式または破損構造
   */
  function parseImageHeaderDetailed(bytes, isFullFile = true) {
    if (!(bytes instanceof Uint8Array) || bytes.length < 24) {
      return { status: 'invalid' };
    }
    const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);

    // 1) PNG: 89 50 4E 47 0D 0A 1A 0A + IHDR (Length=13)
    if (
      bytes[0] === 0x89 && bytes[1] === 0x50 && bytes[2] === 0x4E && bytes[3] === 0x47 &&
      bytes[4] === 0x0D && bytes[5] === 0x0A && bytes[6] === 0x1A && bytes[7] === 0x0A
    ) {
      const ihdrLen = view.getUint32(8, false);
      if (
        ihdrLen === 13 &&
        bytes[12] === 0x49 && bytes[13] === 0x48 &&
        bytes[14] === 0x44 && bytes[15] === 0x52
      ) {
        const width = view.getUint32(16, false);
        const height = view.getUint32(20, false);
        if (width === 0 || height === 0) return { status: 'invalid' };
        return { status: 'ok', mime: 'image/png', width, height };
      }
      return { status: 'invalid' };
    }

    // 2) WebP: "RIFF" .... "WEBP"
    if (
      bytes[0] === 0x52 && bytes[1] === 0x49 && bytes[2] === 0x46 && bytes[3] === 0x46 &&
      bytes[8] === 0x57 && bytes[9] === 0x45 && bytes[10] === 0x42 && bytes[11] === 0x50
    ) {
      if (bytes.length < 30) return { status: 'invalid' };
      const riffSize = view.getUint32(4, true);
      if (riffSize < 20) return { status: 'invalid' };

      const c0 = bytes[12], c1 = bytes[13], c2 = bytes[14], c3 = bytes[15];

      // VP8 (Lossy): 'VP8 '
      if (c0 === 0x56 && c1 === 0x50 && c2 === 0x38 && c3 === 0x20) {
        if (bytes[23] === 0x9D && bytes[24] === 0x01 && bytes[25] === 0x2A) {
          const width = view.getUint16(26, true) & 0x3FFF;
          const height = view.getUint16(28, true) & 0x3FFF;
          if (width === 0 || height === 0) return { status: 'invalid' };
          return { status: 'ok', mime: 'image/webp', width, height };
        }
        return { status: 'invalid' };
      }
      // VP8L (Lossless): 'VP8L'
      if (c0 === 0x56 && c1 === 0x50 && c2 === 0x38 && c3 === 0x4C) {
        if (bytes[20] === 0x2F) {
          const bits = view.getUint32(21, true);
          const width = (bits & 0x3FFF) + 1;
          const height = ((bits >>> 14) & 0x3FFF) + 1;
          return { status: 'ok', mime: 'image/webp', width, height };
        }
        return { status: 'invalid' };
      }
      // VP8X (Extended): 'VP8X'
      if (c0 === 0x56 && c1 === 0x50 && c2 === 0x38 && c3 === 0x58) {
        const width = (bytes[24] | (bytes[25] << 8) | (bytes[26] << 16)) + 1;
        const height = (bytes[27] | (bytes[28] << 8) | (bytes[29] << 16)) + 1;
        return { status: 'ok', mime: 'image/webp', width, height };
      }
      return { status: 'invalid' };
    }

    // 3) JPEG: FF D8 FF
    if (bytes[0] === 0xFF && bytes[1] === 0xD8 && bytes[2] === 0xFF) {
      let offset = 2;
      const limit = bytes.length;
      while (offset < limit) {
        // セグメント境界は必ず 0xFF で始まる必要がある（非同期・破損データの誤検知防止）
        if (bytes[offset] !== 0xFF) {
          return { status: 'invalid' };
        }
        // 連続するパディング 0xFF をスキップ
        while (offset < limit && bytes[offset] === 0xFF) {
          offset++;
        }
        if (offset >= limit) {
          return isFullFile ? { status: 'invalid' } : { status: 'need_more' };
        }
        const marker = bytes[offset++];

        // 0x00 はエスケープバイトでありセグメント境界には現れない。EOI(0xD9)やSOS(0xDA)到達もSOF未検出エラー
        if (marker === 0x00 || marker === 0xD9 || marker === 0xDA) {
          return { status: 'invalid' };
        }
        // ペイロード長を持たない単独マーカー (SOI=0xD8, TEM=0x01, RST0..RST7=0xD0..0xD7)
        if (marker === 0xD8 || marker === 0x01 || (marker >= 0xD0 && marker <= 0xD7)) {
          continue;
        }

        if (offset + 2 > limit) {
          return isFullFile ? { status: 'invalid' } : { status: 'need_more' };
        }
        const segLen = view.getUint16(offset, false);
        if (segLen < 2) {
          return { status: 'invalid' };
        }

        // SOF0〜SOF15 (ただし DHT=0xC4, JPG=0xC8, DAC=0xCC を除く)
        if (
          marker >= 0xC0 && marker <= 0xCF &&
          marker !== 0xC4 && marker !== 0xC8 && marker !== 0xCC
        ) {
          if (segLen < 8) {
            return { status: 'invalid' };
          }
          if (offset + 7 > limit) {
            return isFullFile ? { status: 'invalid' } : { status: 'need_more' };
          }
          const height = view.getUint16(offset + 3, false);
          const width = view.getUint16(offset + 5, false);
          if (width === 0 || height === 0) return { status: 'invalid' };
          return { status: 'ok', mime: 'image/jpeg', width, height };
        }

        offset += segLen;
        if (offset > limit) {
          return isFullFile ? { status: 'invalid' } : { status: 'need_more' };
        }
      }
      return isFullFile ? { status: 'invalid' } : { status: 'need_more' };
    }

    return { status: 'invalid' };
  }

  /**
   * 段階的にファイルをスライスしてヘッダを解析する（巨大EXIFを持つJPEGにも対応）
   */
  async function inspectFileHeader(file) {
    const steps = [64 * 1024, 512 * 1024, 4 * 1024 * 1024, file.size];
    let prevLen = 0;

    for (const rawLimit of steps) {
      const sliceLen = Math.min(file.size, rawLimit);
      if (sliceLen <= prevLen && prevLen > 0) continue;
      prevLen = sliceLen;

      const isFull = sliceLen >= file.size;
      const bytes = new Uint8Array(await file.slice(0, sliceLen).arrayBuffer());
      const res = parseImageHeaderDetailed(bytes, isFull);

      if (res.status === 'ok') {
        return { mime: res.mime, width: res.width, height: res.height };
      }
      if (res.status === 'invalid' || isFull) {
        return null;
      }
      // status === 'need_more' の場合は次のチャンクサイズへ進む
    }
    return null;
  }

  /**
   * 単一バッファからの簡易ラッパー（テスト・同期呼び出し用）
   */
  function parseImageHeader(bytes) {
    const res = parseImageHeaderDetailed(bytes, true);
    return res.status === 'ok' ? { mime: res.mime, width: res.width, height: res.height } : null;
  }

  /**
   * ヘッダ解析結果またはデコード後の寸法が安全上限内か検証する
   */
  function validateDimensions(info) {
    if (!info || !Number.isInteger(info.width) || !Number.isInteger(info.height)) {
      throw new UserFacingError('対応していないファイル形式か、画像ヘッダを読み取れません（JPEG・PNG・WebPのみ対応）。');
    }
    if (info.width < 16 || info.height < 16) {
      throw new UserFacingError('画像サイズが小さすぎます（縦横16px以上の画像を選択してください）。');
    }
    if (info.width > MAX_DIMENSION || info.height > MAX_DIMENSION) {
      throw new UserFacingError(`画像の片辺が上限（${MAX_DIMENSION.toLocaleString()}px）を超えています。`);
    }
    if (info.width * info.height > MAX_INPUT_PIXELS) {
      throw new UserFacingError('画像の画素数が上限（5,000万画素）を超えています。縮小してからお試しください。');
    }
    return true;
  }

  /**
   * Instagram仕様に準拠した横幅基準（1080px / 1440px）またはオリジナル解像度の出力寸法を計算
   */
  function computeOutputDimensions(preset, ratio, singleCropWidth) {
    let outW;
    if (preset === 'original') {
      outW = Math.max(1, Math.round(singleCropWidth));
    } else {
      outW = Number(preset) || 1080;
    }
    const outH = Math.max(1, Math.round(outW / ratio));
    return { outW, outH };
  }

  /**
   * 切り抜き枠の最大寸法と指定スケールでの枠を計算
   */
  function computeCropBox(imgW, imgH, tileCount, singleRatio, scalePct, prevCrop = null) {
    const pct = Math.max(MIN_SCALE_PCT, Math.min(100, Math.round(scalePct)));
    const maxH = Math.min(imgH, imgW / (tileCount * singleRatio));
    const maxW = maxH * singleRatio;
    const factor = pct / 100;
    const w = maxW * factor;
    const h = maxH * factor;

    let x, y;
    if (prevCrop) {
      const centerX = prevCrop.x + (prevCrop.w * tileCount) / 2;
      const centerY = prevCrop.y + prevCrop.h / 2;
      x = centerX - (w * tileCount) / 2;
      y = centerY - h / 2;
    } else {
      x = (imgW - w * tileCount) / 2;
      y = (imgH - h) / 2;
    }

    x = Math.max(0, Math.min(imgW - w * tileCount, x));
    y = Math.max(0, Math.min(imgH - h, y));
    return { x, y, w, h, pct };
  }

  /**
   * 全体収め（余白追加）モード時の仮想ステージ領域を計算
   */
  function computePadStage(imgW, imgH, tileCount, singleRatio) {
    const totalRatio = tileCount * singleRatio;
    const imgRatio = imgW / imgH;
    let totalW, totalH;
    if (imgRatio >= totalRatio) {
      totalW = imgW;
      totalH = imgW / totalRatio;
    } else {
      totalH = imgH;
      totalW = imgH * totalRatio;
    }
    const singleW = totalW / tileCount;
    const x = (imgW - totalW) / 2;
    const y = (imgH - totalH) / 2;
    return { x, y, w: singleW, h: totalH };
  }

  // CRC32 計算テーブル
  const CRC_TABLE = (() => {
    const t = new Uint32Array(256);
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) {
        c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
      }
      t[n] = c >>> 0;
    }
    return t;
  })();

  function crc32(bytes) {
    let c = 0xffffffff;
    for (let i = 0; i < bytes.length; i++) {
      c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
    }
    return (c ^ 0xffffffff) >>> 0;
  }

  /**
   * 無圧縮ZIP（Store）を構築しつつ、渡された entries のバッファ参照を順次解放してピークメモリを抑える
   */
  function buildStoreZipAndConsume(entries) {
    const enc = new TextEncoder();
    const blobParts = [];
    const centralParts = [];
    let offset = 0;
    const fileCount = entries.length;

    const now = new Date();
    const year = Math.max(1980, now.getFullYear());
    const dosTime = ((now.getHours() & 0x1f) << 11) | ((now.getMinutes() & 0x3f) << 5) | ((now.getSeconds() >> 1) & 0x1f);
    const dosDate = (((year - 1980) & 0x7f) << 9) | (((now.getMonth() + 1) & 0x0f) << 5) | (now.getDate() & 0x1f);

    const makeHeader = (length, writer) => {
      const buf = new Uint8Array(length);
      writer(new DataView(buf.buffer));
      return buf;
    };

    for (let i = 0; i < fileCount; i++) {
      const entry = entries[i];
      const nameBytes = enc.encode(entry.name);
      const data = entry.bytes;
      const dataLen = data.byteLength;
      const crc = crc32(data);

      const localHeader = makeHeader(30, v => {
        v.setUint32(0, 0x04034b50, true);
        v.setUint16(4, 20, true);
        v.setUint16(6, 0x0800, true);
        v.setUint16(8, 0, true);
        v.setUint16(10, dosTime, true);
        v.setUint16(12, dosDate, true);
        v.setUint32(14, crc, true);
        v.setUint32(18, dataLen, true);
        v.setUint32(22, dataLen, true);
        v.setUint16(26, nameBytes.length, true);
        v.setUint16(28, 0, true);
      });
      blobParts.push(localHeader, nameBytes, data);

      const centralHeader = makeHeader(46, v => {
        v.setUint32(0, 0x02014b50, true);
        v.setUint16(4, 20, true);
        v.setUint16(6, 20, true);
        v.setUint16(8, 0x0800, true);
        v.setUint16(10, 0, true);
        v.setUint16(12, dosTime, true);
        v.setUint16(14, dosDate, true);
        v.setUint32(16, crc, true);
        v.setUint32(20, dataLen, true);
        v.setUint32(24, dataLen, true);
        v.setUint16(28, nameBytes.length, true);
        v.setUint16(30, 0, true);
        v.setUint16(32, 0, true);
        v.setUint16(34, 0, true);
        v.setUint16(36, 0, true);
        v.setUint32(38, 0, true);
        v.setUint32(42, offset, true);
      });
      centralParts.push(centralHeader, nameBytes);
      offset += localHeader.length + nameBytes.length + dataLen;

      entries[i] = null;
    }

    const centralSize = centralParts.reduce((s, b) => s + b.length, 0);
    const eocd = makeHeader(22, v => {
      v.setUint32(0, 0x06054b50, true);
      v.setUint16(8, fileCount, true);
      v.setUint16(10, fileCount, true);
      v.setUint32(12, centralSize, true);
      v.setUint32(16, offset, true);
    });

    const zipBlob = new Blob([...blobParts, ...centralParts, eocd], { type: 'application/zip' });
    blobParts.length = 0;
    centralParts.length = 0;
    return zipBlob;
  }

  /**
   * テスト・検証用：ZIPバイナリを解析し、Local Header / Central Directory / EOCD / CRC32 / 展開データを厳密に検証する
   */
  function verifyZipStructure(zipBytes, expectedFiles) {
    if (!(zipBytes instanceof Uint8Array) || zipBytes.length < 22) return false;
    const view = new DataView(zipBytes.buffer, zipBytes.byteOffset, zipBytes.byteLength);
    const dec = new TextDecoder();

    const eocdOffset = zipBytes.length - 22;
    if (view.getUint32(eocdOffset, true) !== 0x06054b50) return false;
    const totalEntries = view.getUint16(eocdOffset + 10, true);
    const cdSize = view.getUint32(eocdOffset + 12, true);
    const cdOffset = view.getUint32(eocdOffset + 16, true);

    if (totalEntries !== expectedFiles.length) return false;
    if (cdOffset + cdSize !== eocdOffset) return false;

    let localCursor = 0;
    let cdCursor = cdOffset;

    for (let i = 0; i < expectedFiles.length; i++) {
      const exp = expectedFiles[i];
      if (localCursor + 30 > cdOffset) return false;
      if (view.getUint32(localCursor, true) !== 0x04034b50) return false;

      const flags = view.getUint16(localCursor + 6, true);
      const method = view.getUint16(localCursor + 8, true);
      const localCrc = view.getUint32(localCursor + 14, true);
      const compSize = view.getUint32(localCursor + 18, true);
      const uncompSize = view.getUint32(localCursor + 22, true);
      const nameLen = view.getUint16(localCursor + 26, true);
      const extraLen = view.getUint16(localCursor + 28, true);

      if (flags !== 0x0800 || method !== 0) return false;
      if (compSize !== exp.bytes.length || uncompSize !== exp.bytes.length) return false;

      const nameStart = localCursor + 30;
      const dataStart = nameStart + nameLen + extraLen;
      const dataEnd = dataStart + compSize;
      if (dataEnd > cdOffset) return false;

      const actualName = dec.decode(zipBytes.subarray(nameStart, nameStart + nameLen));
      if (actualName !== exp.name) return false;

      const actualData = zipBytes.subarray(dataStart, dataEnd);
      const expectedCrc = crc32(exp.bytes);
      if (localCrc !== expectedCrc || crc32(actualData) !== expectedCrc) return false;

      for (let b = 0; b < exp.bytes.length; b++) {
        if (actualData[b] !== exp.bytes[b]) return false;
      }

      if (cdCursor + 46 > eocdOffset) return false;
      if (view.getUint32(cdCursor, true) !== 0x02014b50) return false;
      const cdCrc = view.getUint32(cdCursor + 16, true);
      const cdCompSize = view.getUint32(cdCursor + 20, true);
      const cdNameLen = view.getUint16(cdCursor + 28, true);
      const cdExtraLen = view.getUint16(cdCursor + 30, true);
      const cdCommentLen = view.getUint16(cdCursor + 32, true);
      const cdLocalOffset = view.getUint32(cdCursor + 42, true);

      if (cdCrc !== expectedCrc || cdCompSize !== exp.bytes.length) return false;
      if (cdLocalOffset !== localCursor) return false;
      const cdName = dec.decode(zipBytes.subarray(cdCursor + 46, cdCursor + 46 + cdNameLen));
      if (cdName !== exp.name) return false;

      localCursor = dataEnd;
      cdCursor += 46 + cdNameLen + cdExtraLen + cdCommentLen;
    }

    return localCursor === cdOffset && cdCursor === eocdOffset;
  }

  // =========================================================================
  // 2. UI 制御・設定スナップショット・イベント配線
  // =========================================================================

  const $ = id => document.getElementById(id);
  const fileInput = $('file');
  const dropZone = $('dropZone');
  const sampleBtn = $('sampleBtn');
  const testBtn = $('testBtn');
  const testResultBox = $('testResultBox');
  const canvas = $('canvas');
  const ctx = canvas.getContext('2d', { alpha: false });
  const empty = $('empty');
  const meta = $('fileMeta');
  const operationHint = $('operationHint');
  const countChoices = $('countChoices');
  const ratioSelect = $('ratio');
  const fitModeSelect = $('fitMode');
  const cropControls = $('cropControls');
  const padControls = $('padControls');
  const padColorSelect = $('padColor');
  const zoomRange = $('zoomRange');
  const zoomBadge = $('zoomBadge');
  const countBadge = $('countBadge');
  const sizeSelect = $('size');
  const saveModeSelect = $('saveMode');
  const centerBtn = $('centerBtn');
  const fitBtn = $('fitBtn');
  const resetBtn = $('resetBtn');
  const exportBtn = $('exportBtn');
  const shareBtn = $('shareBtn');
  const status = $('status');
  const thumbs = $('thumbs');

  let source = null;
  let sourceUrl = null;
  let count = 5;
  let scalePct = 100;
  let crop = null;
  let drag = null;
  let loadToken = 0;
  let isBusy = false;

  const supportsFileShare = (() => {
    try {
      if (typeof navigator.canShare !== 'function' || typeof File !== 'function') return false;
      const dummy = new File([new Uint8Array([0])], 'test.jpg', { type: 'image/jpeg' });
      return navigator.canShare({ files: [dummy] });
    } catch {
      return false;
    }
  })();
  if (supportsFileShare) {
    shareBtn.hidden = false;
  }

  for (let i = 2; i <= 10; i++) {
    const b = document.createElement('button');
    b.type = 'button';
    b.textContent = String(i);
    b.setAttribute('aria-pressed', String(i === count));
    b.setAttribute('aria-label', `${i}枚に分割`);
    b.addEventListener('click', () => {
      if (isBusy) return;
      setCount(i);
      if (source) {
        recalculateBox(true);
        render();
      }
    });
    countChoices.appendChild(b);
  }

  function setCount(newCount) {
    count = Math.max(2, Math.min(10, Number(newCount) || 5));
    countBadge.textContent = `${count}枚`;
    for (const btn of countChoices.children) {
      btn.setAttribute('aria-pressed', String(Number(btn.textContent) === count));
    }
    updateExportButtonLabel();
  }

  function updateExportButtonLabel() {
    const isZip = saveModeSelect.value === 'zip';
    exportBtn.textContent = isZip
      ? `ZIPでまとめて保存（${count}枚）`
      : `写真を1枚ずつ保存（${count}枚）`;
  }

  function announce(msg, isError = false) {
    status.textContent = msg;
    status.classList.toggle('error', Boolean(isError));
  }

  /**
   * 書き出し中・読み込み中・テスト実行中に全UIコントロールを一括で有効/無効化する
   */
  function syncControlsState() {
    const hasImage = Boolean(source);
    const isPad = fitModeSelect.value === 'pad';

    fileInput.disabled = isBusy;
    dropZone.classList.toggle('disabled', isBusy);
    sampleBtn.disabled = isBusy;
    testBtn.disabled = isBusy;
    ratioSelect.disabled = isBusy;
    fitModeSelect.disabled = isBusy;
    padColorSelect.disabled = isBusy;
    sizeSelect.disabled = isBusy;
    saveModeSelect.disabled = isBusy;

    for (const btn of countChoices.children) {
      btn.disabled = isBusy;
    }

    const canOperateImage = hasImage && !isBusy;
    exportBtn.disabled = !canOperateImage;
    shareBtn.disabled = !canOperateImage;
    resetBtn.disabled = !canOperateImage;

    const canOperateCrop = canOperateImage && !isPad;
    zoomRange.disabled = !canOperateCrop;
    centerBtn.disabled = !canOperateCrop;
    fitBtn.disabled = !canOperateCrop;
  }

  function setBusyState(busy) {
    isBusy = Boolean(busy);
    if (isBusy && drag) {
      drag = null;
    }
    syncControlsState();
  }

  /**
   * 現在のUI設定と切り抜き座標を不変（Immutable）スナップショットとして取得する
   */
  function captureExportConfig() {
    if (!source || !crop) return null;
    const ratioKey = ratioSelect.value;
    const ratioVal = RATIOS[ratioKey] || (4 / 5);
    return Object.freeze({
      sourceRef: source,
      sourceW: source.width,
      sourceH: source.height,
      count,
      ratio: ratioVal,
      fitMode: fitModeSelect.value,
      padColor: padColorSelect.value,
      sizePreset: sizeSelect.value,
      saveMode: saveModeSelect.value,
      crop: Object.freeze({
        x: crop.x,
        y: crop.y,
        w: crop.w,
        h: crop.h
      })
    });
  }

  function clearSource() {
    if (source) {
      if (typeof source.close === 'function') {
        try { source.close(); } catch {}
      }
      source = null;
    }
    if (sourceUrl) {
      try { URL.revokeObjectURL(sourceUrl); } catch {}
      sourceUrl = null;
    }
    crop = null;
    drag = null;
    thumbs.replaceChildren();
    canvas.width = 0;
    canvas.height = 0;
    canvas.hidden = true;
    empty.hidden = false;
    syncControlsState();
  }

  function recalculateBox(keepCenter = true) {
    if (!source) return;
    const r = RATIOS[ratioSelect.value] || (4 / 5);
    if (fitModeSelect.value === 'pad') {
      crop = computePadStage(source.width, source.height, count, r);
    } else {
      const box = computeCropBox(source.width, source.height, count, r, scalePct, keepCenter ? crop : null);
      scalePct = box.pct;
      zoomRange.value = String(scalePct);
      zoomBadge.textContent = `${scalePct}%`;
      crop = { x: box.x, y: box.y, w: box.w, h: box.h };
    }
  }

  function drawTileWithConfig(targetCtx, cfg, tileIndex, destW, destH) {
    const bgColor = cfg.fitMode === 'pad' ? cfg.padColor : '#ffffff';
    targetCtx.fillStyle = bgColor;
    targetCtx.fillRect(0, 0, destW, destH);

    const tileSrcX = cfg.crop.x + cfg.crop.w * tileIndex;
    const tileSrcY = cfg.crop.y;
    const tileSrcW = cfg.crop.w;
    const tileSrcH = cfg.crop.h;

    const intersectX0 = Math.max(0, tileSrcX);
    const intersectY0 = Math.max(0, tileSrcY);
    const intersectX1 = Math.min(cfg.sourceW, tileSrcX + tileSrcW);
    const intersectY1 = Math.min(cfg.sourceH, tileSrcY + tileSrcH);

    if (intersectX1 > intersectX0 && intersectY1 > intersectY0) {
      const sx = intersectX0;
      const sy = intersectY0;
      const sw = intersectX1 - intersectX0;
      const sh = intersectY1 - intersectY0;

      const dx = ((sx - tileSrcX) / tileSrcW) * destW;
      const dy = ((sy - tileSrcY) / tileSrcH) * destH;
      const dw = (sw / tileSrcW) * destW;
      const dh = (sh / tileSrcH) * destH;

      targetCtx.drawImage(cfg.sourceRef, sx, sy, sw, sh, dx, dy, dw, dh);
    }
  }

  function draw(updateThumbs = true) {
    if (!source || !crop) return;
    const preview = $('preview');
    const maxW = Math.max(220, preview.clientWidth - 4);
    const maxH = Math.max(180, Math.min(window.innerHeight * 0.62, 640));

    if (fitModeSelect.value === 'pad') {
      const totalW = crop.w * count;
      const totalH = crop.h;
      const scale = Math.min(maxW / totalW, maxH / totalH, 1);
      const dispW = Math.max(1, Math.round(totalW * scale));
      const dispH = Math.max(1, Math.round(totalH * scale));

      canvas.width = dispW;
      canvas.height = dispH;
      canvas.style.width = dispW + 'px';
      canvas.style.height = dispH + 'px';

      ctx.fillStyle = padColorSelect.value;
      ctx.fillRect(0, 0, dispW, dispH);

      const dx = (-crop.x / totalW) * dispW;
      const dy = (-crop.y / totalH) * dispH;
      const dw = (source.width / totalW) * dispW;
      const dh = (source.height / totalH) * dispH;
      ctx.drawImage(source, 0, 0, source.width, source.height, dx, dy, dw, dh);

      ctx.save();
      ctx.strokeStyle = '#697b43';
      ctx.lineWidth = 2;
      ctx.strokeRect(1, 1, dispW - 2, dispH - 2);
      for (let i = 1; i < count; i++) {
        const lineX = (dispW / count) * i;
        ctx.beginPath();
        ctx.setLineDash([5, 4]);
        ctx.moveTo(lineX, 0);
        ctx.lineTo(lineX, dispH);
        ctx.stroke();
      }
      ctx.restore();
    } else {
      const scale = Math.min(maxW / source.width, maxH / source.height, 1);
      const dispW = Math.max(1, Math.round(source.width * scale));
      const dispH = Math.max(1, Math.round(source.height * scale));

      canvas.width = dispW;
      canvas.height = dispH;
      canvas.style.width = dispW + 'px';
      canvas.style.height = dispH + 'px';

      const sx = dispW / source.width;
      const sy = dispH / source.height;

      ctx.drawImage(source, 0, 0, dispW, dispH);
      ctx.save();
      ctx.fillStyle = 'rgba(20, 32, 14, 0.55)';
      ctx.fillRect(0, 0, dispW, dispH);

      const cx = crop.x * sx;
      const cy = crop.y * sy;
      const cw = crop.w * count * sx;
      const ch = crop.h * sy;

      ctx.drawImage(source, crop.x, crop.y, crop.w * count, crop.h, cx, cy, cw, ch);

      ctx.strokeStyle = '#f7ffdf';
      ctx.lineWidth = 2;
      ctx.strokeRect(cx, cy, cw, ch);

      for (let i = 0; i < count; i++) {
        const tileX = (crop.x + crop.w * i) * sx;
        if (i > 0) {
          ctx.beginPath();
          ctx.setLineDash([5, 4]);
          ctx.moveTo(tileX, cy);
          ctx.lineTo(tileX, cy + ch);
          ctx.stroke();
          ctx.setLineDash([]);
        }
        const badgeW = 22, badgeH = 18;
        if (cw / count > badgeW + 6 && ch > badgeH + 6) {
          ctx.fillStyle = 'rgba(52, 69, 42, 0.85)';
          ctx.fillRect(tileX + 5, cy + 5, badgeW, badgeH);
          ctx.fillStyle = '#ffffff';
          ctx.font = 'bold 11px system-ui, sans-serif';
          ctx.textAlign = 'center';
          ctx.textBaseline = 'middle';
          ctx.fillText(String(i + 1).padStart(2, '0'), tileX + 5 + badgeW / 2, cy + 5 + badgeH / 2);
        }
      }

      ctx.beginPath();
      ctx.arc(cx + cw, cy + ch, 8, 0, Math.PI * 2);
      ctx.fillStyle = '#697b43';
      ctx.fill();
      ctx.lineWidth = 2.5;
      ctx.strokeStyle = '#ffffff';
      ctx.stroke();
      ctx.restore();
    }

    canvas.hidden = false;
    empty.hidden = true;
    if (updateThumbs) renderThumbs();
  }

  function renderThumbs() {
    thumbs.replaceChildren();
    const cfg = captureExportConfig();
    if (!cfg) return;

    const thumbW = 150;
    const thumbH = Math.max(1, Math.round(thumbW / cfg.ratio));

    const frag = document.createDocumentFragment();
    for (let i = 0; i < cfg.count; i++) {
      const item = document.createElement('div');
      item.className = 'thumb';
      const c = document.createElement('canvas');
      c.width = thumbW;
      c.height = thumbH;
      const tctx = c.getContext('2d', { alpha: false });
      if (tctx) {
        drawTileWithConfig(tctx, cfg, i, thumbW, thumbH);
      }
      const label = document.createElement('span');
      label.textContent = `${String(i + 1).padStart(2, '0')} / ${cfg.count}`;
      item.append(c, label);
      frag.appendChild(item);
    }
    thumbs.appendChild(frag);
  }

  function render() {
    draw(true);
    syncControlsState();
  }

  // =========================================================================
  // 3. 安全な画像ファイル読み込み（読み込み中ロック＋段階的ヘッダ検査＋デコード後再検証）
  // =========================================================================

  async function loadFile(file) {
    if (!file || isBusy) return;
    const currentToken = ++loadToken;
    setBusyState(true);
    clearSource();

    if (file.size > MAX_FILE_BYTES) {
      setBusyState(false);
      announce('ファイルサイズが大きすぎます（上限 40MB まで）。', true);
      fileInput.value = '';
      return;
    }

    announce('ファイルヘッダと画像寸法を検査しています…');
    try {
      const headerInfo = await inspectFileHeader(file);
      if (currentToken !== loadToken) return;

      validateDimensions(headerInfo);

      announce('画像を安全に展開しています…');
      let decodedSource = null;

      if ('createImageBitmap' in window) {
        let bmp;
        try {
          bmp = await createImageBitmap(file, { imageOrientation: 'from-image' });
        } catch {
          throw new UserFacingError('画像のデコードに失敗しました。ファイルが破損しているか非対応の形式です。');
        }
        if (currentToken !== loadToken) {
          bmp.close?.();
          return;
        }
        try {
          validateDimensions({ mime: headerInfo.mime, width: bmp.width, height: bmp.height });
        } catch (err) {
          bmp.close?.();
          throw err;
        }
        decodedSource = bmp;
      } else {
        const tempUrl = URL.createObjectURL(file);
        try {
          const img = new Image();
          img.decoding = 'async';
          await new Promise((resolve, reject) => {
            img.onload = resolve;
            img.onerror = () => reject(new UserFacingError('画像の読み込みに失敗しました。別の画像をお試しください。'));
            img.src = tempUrl;
          });
          if (currentToken !== loadToken) {
            URL.revokeObjectURL(tempUrl);
            return;
          }
          validateDimensions({ mime: headerInfo.mime, width: img.naturalWidth, height: img.naturalHeight });
          sourceUrl = tempUrl;
          decodedSource = img;
        } catch (err) {
          URL.revokeObjectURL(tempUrl);
          throw err;
        }
      }

      source = decodedSource;
      meta.textContent = `読み込み済み：${source.width.toLocaleString()} × ${source.height.toLocaleString()} px · ${(file.size / 1024 / 1024).toFixed(2)} MB (${headerInfo.mime})`;

      scalePct = 100;
      recalculateBox(false);
      draw(true);
      announce('読み込みが完了しました。プレビュー上で位置やサイズを調整できます。');
    } catch (err) {
      if (currentToken !== loadToken) return;
      clearSource();
      const safeMessage = err instanceof UserFacingError
        ? err.message
        : '画像の読み込み中にエラーが発生しました。別の画像ファイルでお試しください。';
      announce(safeMessage, true);
    } finally {
      fileInput.value = '';
      if (currentToken === loadToken) {
        setBusyState(false);
      }
    }
  }

  fileInput.addEventListener('change', () => {
    const f = fileInput.files?.[0];
    if (f) loadFile(f);
  });

  for (const evt of ['dragenter', 'dragover']) {
    dropZone.addEventListener(evt, e => {
      e.preventDefault();
      if (!isBusy) dropZone.classList.add('dragover');
    });
  }
  for (const evt of ['dragleave', 'drop']) {
    dropZone.addEventListener(evt, e => {
      e.preventDefault();
      dropZone.classList.remove('dragover');
    });
  }
  dropZone.addEventListener('drop', e => {
    if (isBusy) return;
    const f = e.dataTransfer?.files?.[0];
    if (f) loadFile(f);
  });

  // サンプルパノラマ生成
  sampleBtn.addEventListener('click', async () => {
    if (isBusy) return;
    setBusyState(true);
    announce('サンプルパノラマ写真を生成しています…');
    let sampleFile = null;
    try {
      const c = document.createElement('canvas');
      c.width = 3600;
      c.height = 1000;
      try {
        const sctx = c.getContext('2d', { alpha: false });
        const sky = sctx.createLinearGradient(0, 0, 0, c.height);
        sky.addColorStop(0, '#2c4832');
        sky.addColorStop(0.45, '#697b43');
        sky.addColorStop(0.75, '#d9c589');
        sky.addColorStop(1, '#f4e8c1');
        sctx.fillStyle = sky;
        sctx.fillRect(0, 0, c.width, c.height);

        sctx.fillStyle = 'rgba(255, 250, 220, 0.85)';
        sctx.beginPath();
        sctx.arc(1950, 420, 130, 0, Math.PI * 2);
        sctx.fill();

        const layers = [
          { yBase: 620, amp1: 140, amp2: 65, freq1: 0.0022, freq2: 0.006, color: '#4c5e35' },
          { yBase: 740, amp1: 110, amp2: 45, freq1: 0.0031, freq2: 0.008, color: '#34452a' },
          { yBase: 860, amp1: 60,  amp2: 25, freq1: 0.0045, freq2: 0.012, color: '#1f2b18' }
        ];
        for (const layer of layers) {
          sctx.fillStyle = layer.color;
          sctx.beginPath();
          sctx.moveTo(0, c.height);
          for (let x = 0; x <= c.width; x += 12) {
            const y = layer.yBase
              - Math.sin(x * layer.freq1 + 1.2) * layer.amp1
              - Math.cos(x * layer.freq2) * layer.amp2;
            sctx.lineTo(x, y);
          }
          sctx.lineTo(c.width, c.height);
          sctx.closePath();
          sctx.fill();
        }

        const blob = await canvasToBlob(c, 'image/jpeg', 0.92);
        sampleFile = new File([blob], 'sample.jpg', { type: 'image/jpeg' });
      } finally {
        c.width = 0;
        c.height = 0;
      }
    } catch {
      setBusyState(false);
      announce('サンプル画像の生成に失敗しました。', true);
      return;
    }
    setBusyState(false);
    if (sampleFile) {
      await loadFile(sampleFile);
    }
  });

  // 各種設定変更イベント
  ratioSelect.addEventListener('change', () => {
    if (!source || isBusy) return;
    recalculateBox(true);
    render();
  });

  fitModeSelect.addEventListener('change', () => {
    if (isBusy) return;
    const isPad = fitModeSelect.value === 'pad';
    cropControls.hidden = isPad;
    padControls.hidden = !isPad;
    operationHint.textContent = isPad
      ? '💡 全体収めモード：パノラマ全体が欠けないように中央配置し、上下（または左右）に余白を自動追加します。'
      : '💡 枠内ドラッグ（または矢印キー）で移動、枠の右下「●」ドラッグまたはスライダーで一部切り取り（拡大・縮小）ができます。';
    syncControlsState();
    if (!source) return;
    recalculateBox(false);
    render();
  });

  padColorSelect.addEventListener('change', () => {
    if (!source || isBusy) return;
    render();
  });

  zoomRange.addEventListener('input', () => {
    if (!source || isBusy || fitModeSelect.value === 'pad') return;
    scalePct = Number(zoomRange.value);
    recalculateBox(true);
    draw(false);
  });

  zoomRange.addEventListener('change', () => {
    if (!source || isBusy) return;
    renderThumbs();
  });

  saveModeSelect.addEventListener('change', () => {
    if (isBusy) return;
    updateExportButtonLabel();
  });

  centerBtn.addEventListener('click', () => {
    if (!source || !crop || isBusy || fitModeSelect.value === 'pad') return;
    crop.x = (source.width - crop.w * count) / 2;
    crop.y = (source.height - crop.h) / 2;
    render();
    announce('切り取り枠を中央に揃えました。');
  });

  fitBtn.addEventListener('click', () => {
    if (!source || isBusy || fitModeSelect.value === 'pad') return;
    scalePct = 100;
    recalculateBox(true);
    render();
    announce('切り取り枠を最大サイズに広げました。');
  });

  resetBtn.addEventListener('click', () => {
    if (!source || isBusy) return;
    setCount(5);
    ratioSelect.value = '4:5';
    fitModeSelect.value = 'crop';
    cropControls.hidden = false;
    padControls.hidden = true;
    sizeSelect.value = '1080';
    saveModeSelect.value = 'zip';
    updateExportButtonLabel();
    scalePct = 100;
    recalculateBox(false);
    render();
    announce('設定を初期状態に戻しました。');
  });

  // ポインタ操作（移動・右下ハンドルでのサイズ変更）
  function getSourcePoint(e) {
    const rect = canvas.getBoundingClientRect();
    return {
      x: (e.clientX - rect.left) * (source.width / rect.width),
      y: (e.clientY - rect.top) * (source.height / rect.height),
      scaleCss: rect.width / source.width
    };
  }

  canvas.addEventListener('pointerdown', e => {
    if (!source || !crop || isBusy || fitModeSelect.value === 'pad') return;
    const p = getSourcePoint(e);
    const handleX = crop.x + crop.w * count;
    const handleY = crop.y + crop.h;
    const hitRadius = 18 / Math.max(0.05, p.scaleCss);

    const mode = Math.hypot(p.x - handleX, p.y - handleY) <= hitRadius ? 'resize' : 'move';
    drag = {
      mode,
      startX: p.x,
      startY: p.y,
      initX: crop.x,
      initY: crop.y
    };
    canvas.setPointerCapture(e.pointerId);
  });

  canvas.addEventListener('pointermove', e => {
    if (!drag || !source || !crop || isBusy || fitModeSelect.value === 'pad') return;
    const p = getSourcePoint(e);

    if (drag.mode === 'move') {
      crop.x = Math.max(0, Math.min(source.width - crop.w * count, drag.initX + (p.x - drag.startX)));
      crop.y = Math.max(0, Math.min(source.height - crop.h, drag.initY + (p.y - drag.startY)));
      draw(false);
    } else if (drag.mode === 'resize') {
      const r = RATIOS[ratioSelect.value] || (4 / 5);
      const maxH = Math.min(source.height, source.width / (count * r));
      const maxW = maxH * r;
      const availW = source.width - drag.initX;
      const availH = source.height - drag.initY;

      const byWidth = (p.x - drag.initX) / count;
      const byHeight = (p.y - drag.initY) * r;
      const desiredSingleW = Math.max(byWidth, byHeight);

      const minW = maxW * (MIN_SCALE_PCT / 100);
      const limitW = Math.min(maxW, availW / count, availH * r);

      crop.w = Math.max(minW, Math.min(limitW, desiredSingleW));
      crop.h = crop.w / r;
      scalePct = Math.max(MIN_SCALE_PCT, Math.min(100, Math.round((crop.h / maxH) * 100)));
      zoomRange.value = String(scalePct);
      zoomBadge.textContent = `${scalePct}%`;
      draw(false);
    }
  });

  for (const evt of ['pointerup', 'pointercancel', 'lostpointercapture']) {
    canvas.addEventListener(evt, () => {
      if (drag) {
        drag = null;
        if (source && crop && !isBusy) renderThumbs();
      }
    });
  }

  // キーボード矢印キーによる枠移動
  canvas.addEventListener('keydown', e => {
    if (!source || !crop || isBusy || fitModeSelect.value === 'pad') return;
    const step = (e.shiftKey ? 20 : 4) * (source.width / 1000);
    let moved = true;
    switch (e.key) {
      case 'ArrowLeft':  crop.x -= step; break;
      case 'ArrowRight': crop.x += step; break;
      case 'ArrowUp':    crop.y -= step; break;
      case 'ArrowDown':  crop.y += step; break;
      default: moved = false;
    }
    if (moved) {
      e.preventDefault();
      crop.x = Math.max(0, Math.min(source.width - crop.w * count, crop.x));
      crop.y = Math.max(0, Math.min(source.height - crop.h, crop.y));
      draw(true);
    }
  });

  // =========================================================================
  // 4. 分割画像の生成・保存・共有（スナップショット固定＋省メモリ逐次処理）
  // =========================================================================

  function canvasToBlob(c, type = 'image/jpeg', quality = 0.94) {
    return new Promise((resolve, reject) => {
      c.toBlob(b => (b ? resolve(b) : reject(new UserFacingError('画像の書き出しに失敗しました。'))), type, quality);
    });
  }

  function triggerDownload(blob, filename) {
    const u = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = u;
    a.download = filename;
    a.rel = 'noopener';
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => {
      try { URL.revokeObjectURL(u); } catch {}
    }, 60000);
  }

  function validateAndGetOutputSize(cfg) {
    const { outW, outH } = computeOutputDimensions(cfg.sizePreset, cfg.ratio, cfg.crop.w);
    if (!Number.isSafeInteger(outW) || !Number.isSafeInteger(outH) || outW < 1 || outH < 1 || outW * outH > MAX_SINGLE_OUTPUT_PIXELS) {
      throw new UserFacingError('出力画像サイズが大きすぎます。「標準（横幅 1080px）」を選択してください。');
    }
    if (outW * outH * cfg.count > MAX_TOTAL_OUTPUT_PIXELS) {
      throw new UserFacingError('全画像の合計画素数が上限を超えています。解像度を下げるか分割枚数を減らしてください。');
    }
    return { outW, outH };
  }

  async function renderSingleTileBlob(cfg, index, outW, outH) {
    const tileCanvas = document.createElement('canvas');
    tileCanvas.width = outW;
    tileCanvas.height = outH;
    try {
      const tctx = tileCanvas.getContext('2d', { alpha: false });
      if (!tctx) throw new UserFacingError('画像処理用のメモリ領域を確保できませんでした。');
      tctx.imageSmoothingEnabled = true;
      tctx.imageSmoothingQuality = 'high';
      drawTileWithConfig(tctx, cfg, index, outW, outH);
      return await canvasToBlob(tileCanvas, 'image/jpeg', 0.94);
    } finally {
      tileCanvas.width = 0;
      tileCanvas.height = 0;
    }
  }

  exportBtn.addEventListener('click', async () => {
    if (!source || !crop || isBusy) return;
    const cfg = captureExportConfig();
    if (!cfg) return;

    setBusyState(true);
    const zipEntries = [];

    try {
      const { outW, outH } = validateAndGetOutputSize(cfg);
      const totalStr = String(cfg.count).padStart(2, '0');
      let totalBytes = 0;

      if (cfg.saveMode === 'zip') {
        for (let i = 0; i < cfg.count; i++) {
          announce(`分割画像を作成しています… (${i + 1} / ${cfg.count}枚目 · ${outW}×${outH}px)`);
          let blob = await renderSingleTileBlob(cfg, i, outW, outH);
          totalBytes += blob.size;
          if (totalBytes > MAX_ZIP_BYTES) {
            blob = null;
            throw new UserFacingError('作成画像の合計容量が上限（80MB）を超えました。標準サイズを選択してください。');
          }
          const bytes = new Uint8Array(await blob.arrayBuffer());
          blob = null;

          const numStr = String(i + 1).padStart(2, '0');
          zipEntries.push({ name: `carousel_${numStr}-of-${totalStr}.jpg`, bytes });
          await new Promise(res => setTimeout(res, 20));
        }

        announce('ZIPファイルをまとめています…');
        const zipBlob = buildStoreZipAndConsume(zipEntries);
        triggerDownload(zipBlob, `carousel_${totalStr}slides.zip`);
        announce(`完了：${cfg.count}枚の画像をZIPで保存しました。番号順（01〜）にInstagramへ追加してください。`);
      } else {
        for (let i = 0; i < cfg.count; i++) {
          announce(`写真を保存しています… (${i + 1} / ${cfg.count}枚目 · ${outW}×${outH}px)`);
          let blob = await renderSingleTileBlob(cfg, i, outW, outH);
          totalBytes += blob.size;
          if (totalBytes > MAX_ZIP_BYTES) {
            blob = null;
            throw new UserFacingError('作成画像の合計容量が上限（80MB）を超えました。標準サイズを選択してください。');
          }
          const numStr = String(i + 1).padStart(2, '0');
          triggerDownload(blob, `carousel_${numStr}-of-${totalStr}.jpg`);
          blob = null;
          await new Promise(res => setTimeout(res, 350));
        }
        announce(`完了：${cfg.count}枚のJPEG画像を個別に保存しました。`);
      }
    } catch (err) {
      const msg = err instanceof UserFacingError ? err.message : '書き出しに失敗しました。画像サイズを小さくして再度お試しください。';
      announce(msg, true);
    } finally {
      for (const entry of zipEntries) {
        if (entry && entry.bytes) {
          try { entry.bytes.fill(0); } catch {}
        }
      }
      zipEntries.length = 0;
      setBusyState(false);
    }
  });

  shareBtn.addEventListener('click', async () => {
    if (!source || !crop || isBusy || !supportsFileShare) return;
    const cfg = captureExportConfig();
    if (!cfg) return;

    setBusyState(true);
    try {
      const { outW, outH } = validateAndGetOutputSize(cfg);
      const totalStr = String(cfg.count).padStart(2, '0');
      const shareFiles = [];
      let totalBytes = 0;

      for (let i = 0; i < cfg.count; i++) {
        announce(`共有用の画像を作成しています… (${i + 1} / ${cfg.count}枚目)`);
        let blob = await renderSingleTileBlob(cfg, i, outW, outH);
        totalBytes += blob.size;
        if (totalBytes > MAX_ZIP_BYTES) {
          blob = null;
          throw new UserFacingError('共有画像の合計容量が上限（80MB）を超えました。');
        }
        const numStr = String(i + 1).padStart(2, '0');
        const name = `carousel_${numStr}-of-${totalStr}.jpg`;
        shareFiles.push(new File([blob], name, { type: 'image/jpeg' }));
        blob = null;
        await new Promise(res => setTimeout(res, 20));
      }

      if (!navigator.canShare({ files: shareFiles })) {
        throw new UserFacingError('お使いのブラウザは複数枚の同時共有に対応していません。ZIPまたは個別保存をご利用ください。');
      }
      announce('共有メニューを開いています…');
      await navigator.share({
        files: shareFiles,
        title: 'パノラマ分割画像',
        text: `Instagramカルーセル用（${cfg.count}枚）`
      });
      announce(`${cfg.count}枚の画像を共有しました。`);
    } catch (err) {
      if (err && err.name === 'AbortError') {
        announce('共有をキャンセルしました。');
      } else {
        const msg = err instanceof UserFacingError ? err.message : '共有に失敗しました。保存ボタンをご利用ください。';
        announce(msg, true);
      }
    } finally {
      setBusyState(false);
    }
  });

  // =========================================================================
  // 5. コアロジック自己診断テストスイート（全20件・非同期バイナリ完全検証）
  // =========================================================================

  async function runSelfTests() {
    if (isBusy) return;
    setBusyState(true);
    const logs = [];
    let passed = 0;
    let total = 0;

    const assert = (name, condition) => {
      total++;
      if (condition) {
        passed++;
        logs.push(`✅ PASS: ${name}`);
      } else {
        logs.push(`❌ FAIL: ${name}`);
      }
    };

    try {
      // Test 1: PNG ヘッダ寸法解析 (4000 x 1000)
      const pngBytes = new Uint8Array([
        0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A,
        0x00, 0x00, 0x00, 0x0D, 0x49, 0x48, 0x44, 0x52,
        0x00, 0x00, 0x0F, 0xA0,
        0x00, 0x00, 0x03, 0xE8,
        0x08, 0x02, 0x00, 0x00, 0x00
      ]);
      const pngInfo = parseImageHeader(pngBytes);
      assert('1. PNG IHDR 寸法解析 (4000×1000)', Boolean(pngInfo && pngInfo.mime === 'image/png' && pngInfo.width === 4000 && pngInfo.height === 1000));

      // Test 2: JPEG SOF0 ヘッダ寸法解析 (3000 x 1500)
      const jpgBytes = new Uint8Array([
        0xFF, 0xD8, 0xFF, 0xE0, 0x00, 0x04, 0x00, 0x00,
        0xFF, 0xC0, 0x00, 0x11, 0x08,
        0x05, 0xDC,
        0x0B, 0xB8,
        0x03, 0x01, 0x22, 0x00, 0x02, 0x11, 0x01, 0x03, 0x11, 0x01
      ]);
      const jpgInfo = parseImageHeader(jpgBytes);
      assert('2. JPEG SOF0 寸法解析 (3000×1500)', Boolean(jpgInfo && jpgInfo.mime === 'image/jpeg' && jpgInfo.width === 3000 && jpgInfo.height === 1500));

      // Test 3: JPEG 段階的チャンク走査境界テスト (先頭チャンクでSOF未到達時に need_more を返すか)
      const partialJpg = jpgBytes.subarray(0, 12);
      const partialRes = parseImageHeaderDetailed(partialJpg, false);
      const fullFailRes = parseImageHeaderDetailed(partialJpg, true);
      assert('3. JPEG 境界検査 (部分チャンク=need_more / 破損終端=invalid)', partialRes.status === 'need_more' && fullFailRes.status === 'invalid');

      // Test 4: 巨大APP1(EXIF 80KB)を含むJPEGでの段階的 inspectFileHeader 検証
      const bigExifJpg = new Uint8Array(70000);
      bigExifJpg.set([0xFF, 0xD8, 0xFF, 0xE1, 0xFF, 0xFE]); // APP1 length = 65534 bytes
      // offset 4 + 65534 = 65538 に SOF0 (width=2000, height=800) を配置
      bigExifJpg.set([0xFF, 0xC0, 0x00, 0x11, 0x08, 0x03, 0x20, 0x07, 0xD0, 0x03, 0x01, 0x22, 0x00, 0x02, 0x11, 0x01, 0x03, 0x11, 0x01], 65538);
      const bigExifFile = new File([bigExifJpg], 'exif.jpg', { type: 'image/jpeg' });
      const bigExifInfo = await inspectFileHeader(bigExifFile);
      assert('4. 64KB超のEXIFを持つJPEGの段階的チャンク解析 (2000×800)', Boolean(bigExifInfo && bigExifInfo.width === 2000 && bigExifInfo.height === 800));

      // Test 5: JPEG セグメント境界の非0xFF不正データ拒否（偽装SOF誤認防止）
      const desyncJpg = new Uint8Array([
        0xFF, 0xD8, 0xFF, 0xE0, 0x00, 0x04, 0x00, 0x00,
        0x12, 0x34, // 本来0xFFであるべき位置に非0xFF
        0xFF, 0xC0, 0x00, 0x11, 0x08, 0x05, 0xDC, 0x0B, 0xB8
      ]);
      assert('5. JPEG セグメント境界ずれ（非0xFF）の厳格拒否', parseImageHeader(desyncJpg) === null);

      // Test 6: WebP VP8X ヘッダ寸法解析 (2500 x 800)
      const webpBytes = new Uint8Array([
        0x52, 0x49, 0x46, 0x46, 0x24, 0x00, 0x00, 0x00,
        0x57, 0x45, 0x42, 0x50, 0x56, 0x50, 0x38, 0x58,
        0x0A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xC3, 0x09, 0x00, 0x1F, 0x03, 0x00
      ]);
      const webpInfo = parseImageHeader(webpBytes);
      assert('6. WebP VP8X 寸法解析 (2500×800)', Boolean(webpInfo && webpInfo.mime === 'image/webp' && webpInfo.width === 2500 && webpInfo.height === 800));

      // Test 7: WebP VP8L (Lossless) ヘッダ寸法解析 (1000 x 500)
      const webpLBytes = new Uint8Array(30);
      webpLBytes.set([0x52, 0x49, 0x46, 0x46, 0x20, 0, 0, 0, 0x57, 0x45, 0x42, 0x50, 0x56, 0x50, 0x38, 0x4C, 8, 0, 0, 0, 0x2F]);
      new DataView(webpLBytes.buffer).setUint32(21, 999 | (499 << 14), true);
      const webpLInfo = parseImageHeader(webpLBytes);
      assert('7. WebP VP8L 寸法解析 (1000×500)', Boolean(webpLInfo && webpLInfo.width === 1000 && webpLInfo.height === 500));

      // Test 8: 異常データ拒否（幅0pxの破損PNGおよび不正シグネチャ）
      const zeroWidthPng = new Uint8Array(pngBytes);
      zeroWidthPng[18] = 0;
      zeroWidthPng[19] = 0;
      const fakeBytes = new Uint8Array(30).fill(0x41);
      assert('8. 異常ヘッダ拒否 (0px幅PNG ＆ 偽装ファイル)', parseImageHeader(zeroWidthPng) === null && parseImageHeader(fakeBytes) === null);

      // Test 9: デコード前巨大画像（10,000 × 10,000 = 1億画素）の拒否
      let bombBlocked = false;
      try {
        validateDimensions({ mime: 'image/png', width: 10000, height: 10000 });
      } catch {
        bombBlocked = true;
      }
      assert('9. 巨大画像ボム(1億画素)のデコード前拒否', bombBlocked);

      // Test 10: 単辺上限超過 (33,000 × 100) および極小画像 (8 × 8) の拒否
      let edgeBlocked = false;
      let tinyBlocked = false;
      try { validateDimensions({ mime: 'image/png', width: 33000, height: 100 }); } catch { edgeBlocked = true; }
      try { validateDimensions({ mime: 'image/png', width: 8, height: 8 }); } catch { tinyBlocked = true; }
      assert('10. 寸法境界テスト (単辺32,767px超 ＆ 16px未満の拒否)', edgeBlocked && tinyBlocked);

      // Test 11: 出力サイズ 4:5 (標準 1080px → 1080×1350)
      const out45 = computeOutputDimensions('1080', 4 / 5, 500);
      assert('11. 4:5 標準出力サイズ === 1080×1350', out45.outW === 1080 && out45.outH === 1350);

      // Test 12: 出力サイズ 3:4 (標準 1080px → 1080×1440)
      const out34 = computeOutputDimensions('1080', 3 / 4, 500);
      assert('12. 3:4 標準出力サイズ === 1080×1440', out34.outW === 1080 && out34.outH === 1440);

      // Test 13: 出力サイズ 1.91:1 (標準 1080px → 1080×565)
      const outLand = computeOutputDimensions('1080', 1.91, 500);
      assert('13. 1.91:1 標準出力サイズ (1080×565)', outLand.outW === 1080 && outLand.outH === 565);

      // Test 14: 出力サイズ 4:5 (高精細 1440px → 1440×1800)
      const out1440 = computeOutputDimensions('1440', 4 / 5, 500);
      assert('14. 4:5 高精細出力サイズ === 1440×1800', out1440.outW === 1440 && out1440.outH === 1800);

      // Test 15: 切り抜き枠の初期計算と境界クランプ
      const cropBox = computeCropBox(4000, 1000, 4, 1, 100, null);
      assert('15. 切り抜き枠計算 (4000×1000, 4枚, 1:1)', cropBox.w === 1000 && cropBox.h === 1000 && cropBox.x === 0);

      // Test 16: 切り抜き枠の部分縮小 (50%)
      const halfBox = computeCropBox(4000, 1000, 4, 1, 50, cropBox);
      assert('16. 切り抜き枠 50%縮小と中央維持', halfBox.w === 500 && halfBox.h === 500 && halfBox.x === 1000 && halfBox.y === 250);

      // Test 17: 全体収め（余白追加）モードのステージ計算
      const padStage = computePadStage(4000, 500, 4, 1);
      assert('17. 余白追加モード計算 (4000×500, 4枚, 1:1 → 高さ1000, y=-250)', padStage.w === 1000 && padStage.h === 1000 && padStage.y === -250);

      // Test 18: IEEE 802.3 CRC32 既知ベクトル検証 ("123456789" -> 0xCBF43926)
      const asciiNums = new TextEncoder().encode('123456789');
      assert('18. CRC32 既知テストベクトル ("123456789" === 0xCBF43926)', crc32(asciiNums) === 0xCBF43926);

      // Test 19: ZIPバイナリの完全検証（ヘッダ署名・ファイル数・CRC32・展開後のバイト一致・メモリ参照解放）
      const samplePayload1 = new Uint8Array([0xFF, 0xD8, 0xFF, 0xE0, 0x00, 0x10, 0x4A, 0x46, 0x49, 0x46, 0xFF, 0xD9]);
      const samplePayload2 = new Uint8Array([0xFF, 0xD8, 0xFF, 0xDB, 0x00, 0x43, 0x01, 0x02, 0x03, 0x04, 0xFF, 0xD9]);
      const expectedEntries = [
        { name: 'carousel_01-of-02.jpg', bytes: new Uint8Array(samplePayload1) },
        { name: 'carousel_02-of-02.jpg', bytes: new Uint8Array(samplePayload2) }
      ];
      const zipInput = [
        { name: 'carousel_01-of-02.jpg', bytes: new Uint8Array(samplePayload1) },
        { name: 'carousel_02-of-02.jpg', bytes: new Uint8Array(samplePayload2) }
      ];
      const zipBlob = buildStoreZipAndConsume(zipInput);
      const entriesConsumed = zipInput[0] === null && zipInput[1] === null;
      const zipBytes = new Uint8Array(await zipBlob.arrayBuffer());
      const zipValid = verifyZipStructure(zipBytes, expectedEntries);

      const corruptedZip = new Uint8Array(zipBytes);
      corruptedZip[45] ^= 0xFF;
      const corruptionDetected = !verifyZipStructure(corruptedZip, expectedEntries);
      assert('19. ZIP構造・CRC32・展開データ一致・改ざん検知・参照解放', zipValid && corruptionDetected && entriesConsumed);

      // Test 20: ビジーロック時の全入力コントロール無効化確認
      const allLockedDuringTest =
        fileInput.disabled &&
        dropZone.classList.contains('disabled') &&
        sampleBtn.disabled &&
        testBtn.disabled &&
        ratioSelect.disabled &&
        fitModeSelect.disabled &&
        padColorSelect.disabled &&
        sizeSelect.disabled &&
        saveModeSelect.disabled &&
        exportBtn.disabled;
      assert('20. 処理中の全設定欄・ドロップ領域ロック動作', allLockedDuringTest);
    } finally {
      setBusyState(false);
    }

    const failed = total - passed;
    testResultBox.hidden = false;
    testResultBox.textContent =
      `【自己診断テスト結果: ${passed} / ${total} 件合格${failed > 0 ? ` (${failed} 件失敗)` : ''}】\n` +
      logs.join('\n');

    if (failed === 0) {
      announce(`自己診断テスト完了：全 ${total} 件すべてパスしました。`, false);
    } else {
      announce(`自己診断テスト失敗：${total} 件中 ${failed} 件のテストが失敗しました（${passed} 件合格）。`, true);
    }
  }

  testBtn.addEventListener('click', () => {
    runSelfTests();
  });

  if (new URLSearchParams(window.location.search).get('test') === '1') {
    runSelfTests();
  }

  let resizeTimer = 0;
  window.addEventListener('resize', () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => {
      if (source && crop && !isBusy) draw(false);
    }, 100);
  });

  window.addEventListener('pagehide', () => {
    clearTimeout(resizeTimer);
    clearSource();
  });
})();