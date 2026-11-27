// PNG squeeze v2 — lossless PNG encoder.
// Strategy (general algorithms, no per-image tuning):
//  1. Decode the input PNG to RGBA pixels.
//  2. Reduce colour type per image: palette (<=256 colours, luminance-sorted),
//     grey, grey+alpha, RGB, or RGBA as the pixels require.
//  3. Choose scanline filters per row from a small set of strategies, picked by
//     actual zlib size (level 6 proxy), so the choice tracks real deflate cost.
//  4. Compress the filtered bytes with an optimal-parsing DEFLATE encoder:
//     hash-chain longest-match search producing, for every position, the
//     smallest distance achieving each match length (sublen), then a
//     shortest-path dynamic program over literal/match tokens with the cost
//     model refined from the previous parse's Huffman lengths, keeping the
//     best parse by true encoded size. Block-wise dynamic Huffman (with a
//     fixed-Huffman fallback), canonical codes, RLE code-length header.
//  5. Emit a minimal valid PNG (IHDR/PLTE/tRNS/IDAT/IEND, bit depth 8).
// Deterministic: fixed amount of work per instance, no clock reads, no
// environment reads, no network. Node 22, stdlib only.
import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';

const W = 1280, H = 720;
const IDS = ['i001', 'i002', 'i003', 'i004', 'i005', 'i006', 'i007', 'i008'];

// ---------- CRC32 ----------
const CRC_TABLE = new Int32Array(256);
for (let n = 0; n < 256; n++) {
  let c = n;
  for (let k = 0; k < 8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
  CRC_TABLE[n] = c;
}
function crc32(buf, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = (c >>> 8) ^ CRC_TABLE[(c ^ buf[i]) & 255];
  return (c ^ -1) >>> 0;
}
function chunk(type, data) {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, 'ascii');
  data.copy(out, 8);
  out.writeUInt32BE(crc32(out, 4, 8 + data.length), 8 + data.length);
  return out;
}
function adler32(buf) {
  let a = 1, b = 0;
  for (let i = 0; i < buf.length; i++) {
    a = (a + buf[i]) % 65521;
    b = (b + a) % 65521;
  }
  return ((b << 16) | a) >>> 0;
}

// ---------- PNG decode (bit depth 8, any colour type, non-interlaced) ----------
function decodePng(buf) {
  if (buf[0] !== 0x89 || buf[1] !== 0x50) throw new Error('not png');
  let pos = 8;
  let w = 0, h = 0, bitDepth = 0, colorType = 0;
  const idat = [];
  let plte = null, trns = null;
  while (pos + 8 <= buf.length) {
    const len = buf.readUInt32BE(pos);
    const type = buf.toString('ascii', pos + 4, pos + 8);
    const data = buf.subarray(pos + 8, pos + 8 + len);
    if (type === 'IHDR') {
      w = data.readUInt32BE(0); h = data.readUInt32BE(4);
      bitDepth = data[8]; colorType = data[9];
    } else if (type === 'PLTE') plte = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
    pos += 12 + len;
  }
  if (bitDepth !== 8) throw new Error('bit depth');
  const channels = colorType === 0 ? 1 : colorType === 2 ? 3 : colorType === 3 ? 1 : colorType === 4 ? 2 : 4;
  const raw = zlib.inflateSync(Buffer.concat(idat));
  const stride = w * channels;
  const px = Buffer.alloc(w * h * 4);
  let prev = Buffer.alloc(stride);
  for (let y = 0; y < h; y++) {
    const f = raw[y * (stride + 1)];
    const row = raw.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1));
    const cur = Buffer.alloc(stride);
    for (let x = 0; x < stride; x++) {
      const a = x >= channels ? cur[x - channels] : 0;
      const b = prev[x];
      const c = (x >= channels) ? prev[x - channels] : 0;
      let v = row[x];
      if (f === 1) v = (v + a) & 255;
      else if (f === 2) v = (v + b) & 255;
      else if (f === 3) v = (v + ((a + b) >> 1)) & 255;
      else if (f === 4) {
        const p = a + b - c, pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
        v = (v + (pa <= pb && pa <= pc ? a : pb <= pc ? b : c)) & 255;
      }
      cur[x] = v;
    }
    for (let x = 0; x < w; x++) {
      const o = (y * w + x) * 4;
      if (colorType === 0) { px[o] = px[o + 1] = px[o + 2] = cur[x]; px[o + 3] = 255; }
      else if (colorType === 2) { px[o] = cur[x * 3]; px[o + 1] = cur[x * 3 + 1]; px[o + 2] = cur[x * 3 + 2]; px[o + 3] = 255; }
      else if (colorType === 3) {
        const idx = cur[x] * 3;
        px[o] = plte[idx]; px[o + 1] = plte[idx + 1]; px[o + 2] = plte[idx + 2];
        px[o + 3] = trns && idx / 3 < trns.length ? trns[idx / 3] : 255;
      } else if (colorType === 4) { px[o] = px[o + 1] = px[o + 2] = cur[x * 2]; px[o + 3] = cur[x * 2 + 1]; }
      else { px[o] = cur[x * 4]; px[o + 1] = cur[x * 4 + 1]; px[o + 2] = cur[x * 4 + 2]; px[o + 3] = cur[x * 4 + 3]; }
    }
    prev = cur;
  }
  return px;
}

// ---------- colour-type reduction ----------
function represent(px) {
  const colors = new Map();
  let opaque = true, grey = true;
  for (let i = 0; i < px.length; i += 4) {
    const r = px[i], g = px[i + 1], b = px[i + 2], a = px[i + 3];
    if (a !== 255) opaque = false;
    if (!(r === g && g === b)) grey = false;
    const key = (r << 24) | (g << 16) | (b << 8) | a;
    if (!colors.has(key)) colors.set(key, colors.size);
  }
  const nCol = colors.size;
  if (grey && opaque) {
    const rows = Buffer.alloc(W * H);
    for (let p = 0, q = 0; p < px.length; p += 4, q++) rows[q] = px[p];
    return { bpp: 1, rows, type: 0, pal: null, trns: null };
  }
  if (nCol <= 256) {
    // palette sorted by luminance so neighbouring indices are similar colours
    const entries = [...colors.keys()];
    entries.sort((a, b) => {
      const la = 0.299 * ((a >>> 24) & 255) + 0.587 * ((a >>> 16) & 255) + 0.114 * ((a >>> 8) & 255);
      const lb = 0.299 * ((b >>> 24) & 255) + 0.587 * ((b >>> 16) & 255) + 0.114 * ((b >>> 8) & 255);
      return (la - lb) || (a - b);
    });
    const remap = new Map();
    const pal = Buffer.alloc(nCol * 3);
    const trns = Buffer.alloc(nCol);
    let lastNonOpaque = -1;
    entries.forEach((key, ni) => {
      remap.set(key, ni);
      pal[ni * 3] = (key >>> 24) & 255;
      pal[ni * 3 + 1] = (key >>> 16) & 255;
      pal[ni * 3 + 2] = (key >>> 8) & 255;
      const a = key & 255;
      trns[ni] = a;
      if (a !== 255) lastNonOpaque = ni;
    });
    const rows = Buffer.alloc(W * H);
    for (let p = 0, q = 0; p < px.length; p += 4, q++) {
      rows[q] = remap.get((px[p] << 24) | (px[p + 1] << 16) | (px[p + 2] << 8) | px[p + 3]);
    }
    return { bpp: 1, rows, type: 3, pal, trns: lastNonOpaque >= 0 ? trns.subarray(0, lastNonOpaque + 1) : null };
  }
  if (grey) {
    const rows = Buffer.alloc(W * H * 2);
    for (let p = 0, q = 0; p < px.length; p += 4, q += 2) { rows[q] = px[p]; rows[q + 1] = px[p + 3]; }
    return { bpp: 2, rows, type: 4, pal: null, trns: null };
  }
  if (opaque) {
    const rows = Buffer.alloc(W * H * 3);
    for (let p = 0, q = 0; p < px.length; p += 4, q += 3) { rows[q] = px[p]; rows[q + 1] = px[p + 1]; rows[q + 2] = px[p + 2]; }
    return { bpp: 3, rows, type: 2, pal: null, trns: null };
  }
  return { bpp: 4, rows: Buffer.from(px), type: 6, pal: null, trns: null };
}

// ---------- scanline filters ----------
function filterRow(out, row, prev, bpp, f) {
  const n = row.length;
  if (f === 0) { out.set(row); return; }
  for (let x = 0; x < n; x++) {
    const a = x >= bpp ? row[x - bpp] : 0;
    const b = prev ? prev[x] : 0;
    const c = (x >= bpp && prev) ? prev[x - bpp] : 0;
    let pred;
    if (f === 1) pred = a;
    else if (f === 2) pred = b;
    else if (f === 3) pred = (a + b) >> 1;
    else { const p = a + b - c, pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c); pred = pa <= pb && pa <= pc ? a : pb <= pc ? b : c; }
    out[x] = (row[x] - pred) & 255;
  }
}
const LOGCOST = new Float64Array(256);
for (let v = 0; v < 256; v++) { const a = v < 128 ? v : 256 - v; LOGCOST[v] = Math.log2(1 + a) + (a === 0 ? 0 : 1); }
function rowCost(frow, mode) {
  let s = 0;
  if (mode === 'minsum') {
    for (let i = 0; i < frow.length; i++) { const v = frow[i]; s += v < 128 ? v : 256 - v; }
  } else {
    for (let i = 0; i < frow.length; i++) s += LOGCOST[frow[i]];
  }
  return s;
}
function applyFilters(rows, bpp, strategy) {
  const stride = W * bpp;
  const out = Buffer.alloc(H * (stride + 1));
  const tmp = Buffer.alloc(stride);
  let prev = null;
  for (let y = 0; y < H; y++) {
    const row = rows.subarray(y * stride, (y + 1) * stride);
    let f;
    if (strategy.startsWith('fixed')) f = +strategy.slice(5);
    else {
      let best = Infinity, bestF = 0;
      for (let cand = 0; cand < 5; cand++) {
        filterRow(tmp, row, prev, bpp, cand);
        const c = rowCost(tmp, strategy);
        if (c < best) { best = c; bestF = cand; }
      }
      f = bestF;
    }
    filterRow(tmp, row, prev, bpp, f);
    out[y * (stride + 1)] = f;
    tmp.copy(out, y * (stride + 1) + 1);
    prev = row;
  }
  return out;
}

// ---------- optimal-parsing DEFLATE ----------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const LEN_CODE = new Uint8Array(259);
for (let len = 3; len <= 258; len++) { let c = 0; while (c < 28 && LEN_BASE[c + 1] <= len) c++; LEN_CODE[len] = c; }
const DIST_CODE = new Uint8Array(32769);
for (let d = 1; d <= 32768; d++) { let c = 0; while (c < 29 && DIST_BASE[c + 1] <= d) c++; DIST_CODE[d] = c; }
const FIXED_LIT_LEN = new Uint8Array(288);
for (let i = 0; i < 144; i++) FIXED_LIT_LEN[i] = 8;
for (let i = 144; i < 256; i++) FIXED_LIT_LEN[i] = 9;
for (let i = 256; i < 280; i++) FIXED_LIT_LEN[i] = 7;
for (let i = 280; i < 288; i++) FIXED_LIT_LEN[i] = 8;
const FIXED_DIST_LEN = new Uint8Array(32).fill(5);

function buildHuffman(freq, maxBits) {
  const n = freq.length;
  const lengths = new Uint8Array(n);
  let used = 0;
  for (let i = 0; i < n; i++) if (freq[i] > 0) used++;
  if (used === 0) return lengths;
  if (used === 1) {
    let first = -1;
    for (let i = 0; i < n; i++) if (freq[i] > 0) { first = i; break; }
    lengths[first] = 1;
    for (let i = 0; i < n; i++) if (i !== first) { lengths[i] = 1; break; }
    return lengths;
  }
  const order = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) order.push(i);
  order.sort((a, b) => freq[a] - freq[b] || a - b);
  const maxNodes = 2 * used;
  const w = new Float64Array(maxNodes);
  const left = new Int32Array(maxNodes).fill(-1);
  const right = new Int32Array(maxNodes).fill(-1);
  for (let i = 0; i < used; i++) w[i] = freq[order[i]];
  let nn = used, li = 0, ii = used;
  const getMin = () => {
    if (li < used && (ii >= nn || w[li] <= w[ii])) return li++;
    return ii++;
  };
  for (let k = 0; k < used - 1; k++) {
    const a = getMin(), b = getMin();
    w[nn] = w[a] + w[b];
    left[nn] = a; right[nn] = b;
    nn++;
  }
  const root = nn - 1;
  const depth = new Int32Array(nn);
  const stack = [root];
  let maxDepth = 0;
  while (stack.length) {
    const nd = stack.pop();
    const d = depth[nd];
    if (nd < used) { lengths[order[nd]] = d; if (d > maxDepth) maxDepth = d; }
    else { depth[left[nd]] = d + 1; depth[right[nd]] = d + 1; stack.push(left[nd], right[nd]); }
  }
  if (maxDepth <= maxBits) return lengths;
  const blCount = new Int32Array(maxBits + 1);
  let overflow = 0;
  for (let nd = 0; nd < nn; nd++) if (depth[nd] > maxBits) overflow++;
  for (let i = 0; i < n; i++) {
    if (lengths[i]) {
      if (lengths[i] > maxBits) lengths[i] = maxBits;
      blCount[lengths[i]]++;
    }
  }
  while (overflow > 0) {
    let m = maxBits - 1;
    while (m > 0 && blCount[m] === 0) m--;
    if (blCount[m] === 0) break;
    blCount[m]--; blCount[m + 1] += 2; blCount[maxBits]--;
    overflow -= 2;
  }
  const syms = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) syms.push(i);
  syms.sort((a, b) => freq[b] - freq[a] || a - b);
  lengths.fill(0);
  let si = 0;
  for (let b = 1; b <= maxBits; b++) for (let k = 0; k < blCount[b]; k++) lengths[syms[si++]] = b;
  return lengths;
}
function canonicalCodes(lengths) {
  const n = lengths.length;
  let maxLen = 0;
  for (let i = 0; i < n; i++) if (lengths[i] > maxLen) maxLen = lengths[i];
  const blCount = new Int32Array(maxLen + 1);
  for (let i = 0; i < n; i++) if (lengths[i]) blCount[lengths[i]]++;
  const nextCode = new Int32Array(maxLen + 2);
  let code = 0;
  for (let b = 1; b <= maxLen; b++) { code = (code + blCount[b - 1]) << 1; nextCode[b] = code; }
  const codes = new Int32Array(n);
  for (let i = 0; i < n; i++) if (lengths[i]) codes[i] = nextCode[lengths[i]]++;
  for (let i = 0; i < n; i++) {
    const l = lengths[i];
    if (!l) continue;
    let rev = 0, c = codes[i];
    for (let k = 0; k < l; k++) { rev = (rev << 1) | (c & 1); c >>>= 1; }
    codes[i] = rev;
  }
  return codes;
}
class BitWriter {
  constructor(cap) { this.buf = new Uint8Array(cap + 1024); this.pos = 0; this.bitbuf = 0; this.bitcnt = 0; }
  write(code, len) {
    this.bitbuf |= code << this.bitcnt;
    this.bitcnt += len;
    while (this.bitcnt >= 8) { this.buf[this.pos++] = this.bitbuf & 255; this.bitbuf >>>= 8; this.bitcnt -= 8; }
  }
  align() { if (this.bitcnt > 0) { this.buf[this.pos++] = this.bitbuf & 255; this.bitbuf = 0; this.bitcnt = 0; } }
  bytes() { return this.buf.subarray(0, this.pos); }
}

const HASH_BITS = 15, HASH_SIZE = 1 << HASH_BITS, HASH_MASK = HASH_SIZE - 1;
const BLOCK_SIZE = 131072;
const ITERS = 2;
// Chain length: 1024 everywhere. Deep chains matter most for palette/grey
// (few distinct hashes), but RGB/RGBA gain too (i007: 2.4%), and the
// segment-based candidate extraction made the search fast enough to afford it.
function chainFor(bpp) { return 1024; }

function deflateOptimal(data, bpp) {
  const MAX_CHAIN = chainFor(bpp);
  const N = data.length;
  const dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
  const out = new BitWriter(N + 1024);
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(N).fill(-1);
  for (let i = 0; i + 2 < N; i++) {
    const h = (((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & HASH_MASK);
    prev[i] = head[h]; head[h] = i;
  }
  const run = new Uint16Array(N + 1);
  for (let i = N - 1; i >= 0; i--) run[i] = (i + 1 < N && data[i] === data[i + 1]) ? Math.min(259, run[i + 1] + 1) : 1;
  // Range-top lengths: k where the length code changes (LEN_CODE[k] != LEN_CODE[k+1]),
  // plus 258. Candidates are range tops and segment ends only.
  const RANGE_TOPS = [];
  for (let k = 3; k < 258; k++) if (LEN_CODE[k] !== LEN_CODE[k + 1]) RANGE_TOPS.push(k);
  RANGE_TOPS.push(258);
  // Segments of the sublen function: segs is a flat array [endLen, dist, ...]
  // in increasing endLen order; segment j covers lengths (prevEnd+1 .. endLen),
  // the first starting at 3. Recording segments instead of filling a 259-entry
  // sublen array makes candidate extraction O(segments) instead of O(maxLen).
  const segs = [];
  const findSublen = (i, capLen) => {
    if (i + 3 > N) { segs.length = 0; return 0; }
    const maxPossible = Math.min(258, N - i, capLen);
    segs.length = 0;
    let bestLen = 0;
    if (i > 0 && data[i] === data[i - 1]) {
      const rl = Math.min(run[i], maxPossible);
      if (rl >= 3) {
        segs.push(rl, 1);
        bestLen = rl;
        if (rl >= maxPossible) return bestLen;
      }
    }
    let cand = prev[i];
    let chainLimit = MAX_CHAIN, tried = 0;
    while (cand >= 0 && tried++ < chainLimit) {
      const dist = i - cand;
      if (dist > 32768) break;
      if (bestLen === 0) {
        // First verify the 3 bytes the hash promised (collisions exist):
        // if they differ this candidate gives no match of length >= 3.
        if (data[cand] !== data[i] || data[cand + 1] !== data[i + 1] || data[cand + 2] !== data[i + 2]) { cand = prev[cand]; continue; }
        // Bytes 0..2 match. If byte 3 differs, the match is exactly 3 long:
        // record it without a matchLen call.
        if (data[cand + 3] !== data[i + 3]) {
          segs.push(3, dist);
          bestLen = 3;
          cand = prev[cand];
          continue;
        }
      } else if (data[cand + bestLen] !== data[i + bestLen]) { cand = prev[cand]; continue; }
      // matchLen, inlined: longest match of data[i..] against data[cand..].
      let len = 0;
      {
        const maxLen = Math.min(258, N - i);
        const j = cand;
        const lim32 = maxLen - 3;
        while (len < lim32) {
          if (dv.getUint32(j + len, true) !== dv.getUint32(i + len, true)) break;
          len += 4;
        }
        while (len < maxLen && data[j + len] === data[i + len]) len++;
      }
      if (len > bestLen) {
        segs.push(len, dist);
        bestLen = len;
        if (len >= maxPossible) break;
        if (len >= 64) chainLimit = Math.min(chainLimit, tried + 8);
        else if (len >= 16) chainLimit = Math.min(chainLimit, tried + 32);
      }
      cand = prev[cand];
    }
    return bestLen;
  };

  // Encode a token array (including its final EOB 256) as one DEFLATE block.
  const writeBlock = (tokens, isLast) => {
    const { lf, df, nLit, nDist } = parseFreqs(tokens);
    const litLengths = new Uint8Array(288); litLengths.set(buildHuffman(lf.subarray(0, nLit), 15));
    const distLengths = new Uint8Array(32); distLengths.set(buildHuffman(df.subarray(0, nDist), 15));
    const dynSize = estimateSize(tokens, lf, df, nLit, nDist, litLengths, distLengths);
    let fixedBits = 3;
    for (const t of tokens) {
      if (t < 256 || t === 256) fixedBits += FIXED_LIT_LEN[t];
      else { const L = t & 0xffff, D = t >>> 16; fixedBits += FIXED_LIT_LEN[257 + LEN_CODE[L]] + LEN_EXTRA[LEN_CODE[L]] + 5 + DIST_EXTRA[DIST_CODE[D]]; }
    }
    if (Math.ceil(fixedBits / 8) < dynSize) {
      out.write(isLast ? 1 : 0, 1);
      out.write(1, 2);
      const litCodes = canonicalCodes(FIXED_LIT_LEN);
      const distCodes = canonicalCodes(FIXED_DIST_LEN);
      for (const t of tokens) {
        if (t < 256 || t === 256) out.write(litCodes[t], FIXED_LIT_LEN[t]);
        else {
          const L = t & 0xffff, D = t >>> 16;
          const lc = LEN_CODE[L];
          out.write(litCodes[257 + lc], FIXED_LIT_LEN[257 + lc]);
          if (LEN_EXTRA[lc]) out.write(L - LEN_BASE[lc], LEN_EXTRA[lc]);
          const dc = DIST_CODE[D];
          out.write(distCodes[dc], 5);
          if (DIST_EXTRA[dc]) out.write(D - DIST_BASE[dc], DIST_EXTRA[dc]);
        }
      }
    } else {
      const litCodes = canonicalCodes(litLengths);
      const distCodes = canonicalCodes(distLengths);
      const allLens = new Uint8Array(nLit + nDist);
      allLens.set(litLengths.subarray(0, nLit), 0);
      allLens.set(distLengths.subarray(0, nDist), nLit);
      const clSyms = [];
      {
        let i = 0;
        const A = allLens;
        while (i < A.length) {
          const v = A[i];
          let run2 = 1;
          while (i + run2 < A.length && A[i + run2] === v) run2++;
          if (v === 0) {
            let r = run2;
            while (r >= 11) { const take = Math.min(r, 138); clSyms.push([18, take - 11]); r -= take; }
            if (r >= 3) { clSyms.push([17, r - 3]); r = 0; }
            while (r > 0) { clSyms.push([0, 0]); r--; }
          } else {
            clSyms.push([v, 0]);
            let r = run2 - 1;
            while (r >= 3) { const take = Math.min(r, 6); clSyms.push([16, take - 3]); r -= take; }
            while (r > 0) { clSyms.push([v, 0]); r--; }
          }
          i += run2;
        }
      }
      const clFreq = new Int32Array(19);
      for (const s of clSyms) clFreq[s[0]]++;
      const clLens = buildHuffman(clFreq, 7);
      const clCodes = canonicalCodes(clLens);
      const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
      let hclen = 19;
      while (hclen > 4 && clLens[CL_ORDER[hclen - 1]] === 0) hclen--;
      out.write(isLast ? 1 : 0, 1);
      out.write(2, 2);
      out.write(nLit - 257, 5);
      out.write(nDist - 1, 5);
      out.write(hclen - 4, 4);
      for (let k = 0; k < hclen; k++) out.write(clLens[CL_ORDER[k]], 3);
      for (const s of clSyms) {
        out.write(clCodes[s[0]], clLens[s[0]]);
        if (s[0] === 16) out.write(s[1], 2);
        else if (s[0] === 17) out.write(s[1], 3);
        else if (s[0] === 18) out.write(s[1], 7);
      }
      for (const t of tokens) {
        if (t < 256 || t === 256) out.write(litCodes[t], litLengths[t]);
        else {
          const L = t & 0xffff, D = t >>> 16;
          const lc = LEN_CODE[L];
          out.write(litCodes[257 + lc], litLengths[257 + lc]);
          if (LEN_EXTRA[lc]) out.write(L - LEN_BASE[lc], LEN_EXTRA[lc]);
          const dc = DIST_CODE[D];
          out.write(distCodes[dc], distLengths[dc]);
          if (DIST_EXTRA[dc]) out.write(D - DIST_BASE[dc], DIST_EXTRA[dc]);
        }
      }
    }
  };


  let pos = 0;
  while (pos < N) {
    const blockEnd = Math.min(N, pos + BLOCK_SIZE);
    const isLast = blockEnd === N;
    const blen = blockEnd - pos;
    // Precompute match candidates once per block; reused across iterations.
    const candOff = new Int32Array(blen + 1);
    let candData = new Int32Array(blen * 16);
    let candLen = 0;
    for (let i = 0; i < blen; i++) {
      const gi = pos + i;
      const maxLen = findSublen(gi, blen - i);
      candOff[i] = candLen;
      if (maxLen >= 3) {
        let segStart = 3;
        let rt = 0;
        for (let s = 0; s < segs.length; s += 2) {
          const endLen = segs[s], dist = segs[s + 1];
          while (rt < RANGE_TOPS.length && RANGE_TOPS[rt] < segStart) rt++;
          let lastTop = -1;
          let k = rt;
          while (k < RANGE_TOPS.length && RANGE_TOPS[k] <= endLen) {
            if (candLen >= candData.length) {
              const bigger = new Int32Array(candData.length * 2);
              bigger.set(candData);
              candData = bigger;
            }
            candData[candLen++] = (RANGE_TOPS[k] << 16) | dist;
            lastTop = RANGE_TOPS[k];
            k++;
          }
          if (lastTop !== endLen) {
            if (candLen >= candData.length) {
              const bigger = new Int32Array(candData.length * 2);
              bigger.set(candData);
              candData = bigger;
            }
            candData[candLen++] = (endLen << 16) | dist;
          }
          segStart = endLen + 1;
        }
      }
    }
    candOff[blen] = candLen;
    candData = candData.subarray(0, candLen);
    const cost = new Float64Array(blen + 1);
    const choice = new Int32Array(blen + 1);
    const litCost = new Float64Array(288);
    const lenCost = new Float64Array(29);
    const distCost = new Float64Array(30);
    const setCosts = (ll, dl) => {
      for (let i = 0; i < 288; i++) litCost[i] = ll[i] > 0 ? ll[i] : FIXED_LIT_LEN[i];
      for (let c = 0; c < 29; c++) lenCost[c] = (ll[257 + c] > 0 ? ll[257 + c] : FIXED_LIT_LEN[257 + c]) + LEN_EXTRA[c];
      for (let c = 0; c < 30; c++) distCost[c] = (dl[c] > 0 ? dl[c] : 5) + DIST_EXTRA[c];
    };
    setCosts(FIXED_LIT_LEN, FIXED_DIST_LEN);
    let bestParse = null, bestSize = Infinity;
    let parse = null;
    for (let iter = 0; iter < ITERS; iter++) {
      cost.fill(Infinity); cost[0] = 0;
      for (let i = 0; i < blen; i++) {
        const ci = cost[i];
        if (ci === Infinity) continue;
        const gi = pos + i;
        const lc = ci + litCost[data[gi]];
        if (lc < cost[i + 1]) { cost[i + 1] = lc; choice[i + 1] = data[gi]; }
        if (i + 3 <= blen) {
          for (let ci2 = candOff[i]; ci2 < candOff[i + 1]; ci2++) {
            const m = candData[ci2];
            const k = m >>> 16, d = m & 0xffff;
            const cc = ci + lenCost[LEN_CODE[k]] + distCost[DIST_CODE[d]];
            if (cc < cost[i + k]) { cost[i + k] = cc; choice[i + k] = (k << 16) | d; }
          }
        }
      }
      parse = [];
      let i = blen;
      while (i > 0) {
        const ch = choice[i];
        if (ch < 256) { parse.push(ch); i -= 1; }
        else { parse.push((ch >>> 16) | ((ch & 0xffff) << 16)); i -= (ch >>> 16); }
      }
      parse.reverse();
      parse.push(256);
      const { lf, df, nLit, nDist } = parseFreqs(parse);
      const ll2 = buildHuffman(lf.subarray(0, nLit), 15);
      const dl2 = buildHuffman(df.subarray(0, nDist), 15);
      const sizeEst = estimateSize(parse, lf, df, nLit, nDist, ll2, dl2);
      if (sizeEst < bestSize) { bestSize = sizeEst; bestParse = parse; }
      if (iter + 1 < ITERS) {
        const fullLit = new Uint8Array(288); fullLit.set(ll2);
        const fullDist = new Uint8Array(32); fullDist.set(dl2);
        setCosts(fullLit, fullDist);
      }
    }
    parse = bestParse;
    writeBlock(parse, isLast);
    pos = blockEnd;
  }
  out.align();
  return out.bytes();
}
function parseFreqs(parse) {
  const lf = new Int32Array(288), df = new Int32Array(30);
  for (const t of parse) {
    if (t < 256 || t === 256) lf[t]++;
    else { const L = t & 0xffff, D = t >>> 16; lf[257 + LEN_CODE[L]]++; df[DIST_CODE[D]]++; }
  }
  let nLit = 288; while (nLit > 257 && lf[nLit - 1] === 0) nLit--;
  let nDist = 30; while (nDist > 1 && df[nDist - 1] === 0) nDist--;
  return { lf, df, nLit, nDist };
}
function estimateSize(parse, lf, df, nLit, nDist, ll2, dl2) {
  let bits = 3 + 5 + 5 + 4;
  const allLens = new Uint8Array(nLit + nDist);
  allLens.set(ll2.subarray(0, nLit), 0);
  allLens.set(dl2.subarray(0, nDist), nLit);
  const clFreq = new Int32Array(19);
  {
    let ii = 0;
    const A = allLens;
    while (ii < A.length) {
      const v = A[ii];
      let run = 1;
      while (ii + run < A.length && A[ii + run] === v) run++;
      if (v === 0) {
        let r = run;
        while (r >= 11) { clFreq[18]++; r -= Math.min(r, 138); }
        if (r >= 3) { clFreq[17]++; r = 0; }
        clFreq[0] += r;
      } else {
        clFreq[v]++;
        let r = run - 1;
        while (r >= 3) { clFreq[16]++; r -= Math.min(r, 6); }
        clFreq[v] += r;
      }
      ii += run;
    }
  }
  const clLens = buildHuffman(clFreq, 7);
  let hclen = 19;
  const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  while (hclen > 4 && clLens[CL_ORDER[hclen - 1]] === 0) hclen--;
  bits += hclen * 3;
  for (let s = 0; s < 19; s++) bits += clFreq[s] * (clLens[s] || 0);
  {
    let ii = 0;
    const A = allLens;
    while (ii < A.length) {
      const v = A[ii];
      let run = 1;
      while (ii + run < A.length && A[ii + run] === v) run++;
      if (v === 0) {
        let r = run;
        while (r >= 11) { bits += 7; r -= Math.min(r, 138); }
        if (r >= 3) bits += 3;
      } else {
        let r = run - 1;
        while (r >= 3) { bits += 2; r -= Math.min(r, 6); }
      }
      ii += run;
    }
  }
  for (let s = 0; s < nLit; s++) bits += lf[s] * (ll2[s] || 0);
  for (let s = 0; s < nDist; s++) bits += df[s] * (dl2[s] || 0);
  for (const t of parse) {
    if (t < 256 || t === 256) continue;
    const L = t & 0xffff, D = t >>> 16;
    bits += LEN_EXTRA[LEN_CODE[L]] + DIST_EXTRA[DIST_CODE[D]];
  }
  return Math.ceil(bits / 8);
}

// ---------- PNG encode ----------
function encodePng(rep, filtered) {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(W, 0);
  ihdr.writeUInt32BE(H, 4);
  ihdr[8] = 8; ihdr[9] = rep.type; ihdr[10] = 0; ihdr[11] = 0; ihdr[12] = 0;
  const parts = [Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]), chunk('IHDR', ihdr)];
  if (rep.type === 3) {
    parts.push(chunk('PLTE', rep.pal));
    if (rep.trns) parts.push(chunk('tRNS', rep.trns));
  }
  const deflated = deflateOptimal(filtered, rep.bpp);
  const z = Buffer.alloc(2 + deflated.length + 4);
  z[0] = 0x78; z[1] = 0x9c;
  z.set(deflated, 2);
  z.writeUInt32BE(adler32(filtered), 2 + deflated.length);
  parts.push(chunk('IDAT', z));
  parts.push(chunk('IEND', Buffer.alloc(0)));
  return Buffer.concat(parts);
}

// ---------- per-instance pipeline ----------
function processInstance(id) {
  const inputPath = path.join('/input', id, 'image.png');
  const buf = fs.readFileSync(inputPath);
  const px = decodePng(buf);
  const rep = represent(px);
  // pick filter strategy by zlib level-6 size (fast proxy for real deflate cost)
  let best = null;
  for (const strat of ['fixed0', 'fixed4', 'minsum', 'entropy']) {
    const filtered = applyFilters(rep.rows, rep.bpp, strat);
    const comp = zlib.deflateSync(filtered, { level: 6 });
    if (!best || comp.length < best.size) best = { strat, filtered, size: comp.length };
  }
  const png = encodePng(rep, best.filtered);
  const outDir = path.join('/output', id);
  fs.mkdirSync(outDir, { recursive: true });
  fs.writeFileSync(path.join(outDir, 'image.png'), png);
  return { id, type: rep.type, strat: best.strat, bytes: png.length };
}

function main() {
  try { fs.appendFileSync('/tmp/bot-debug.log', 'START\n'); } catch (e) {}
  const results = [];
  for (const id of IDS) {
    try {
      const r = processInstance(id);
      try { fs.appendFileSync('/tmp/bot-debug.log', 'DONE ' + id + ' ' + r.bytes + '\n'); } catch (e) {}
      results.push(r);
    } catch (e) {
      // never leave an instance unanswered: fall back to a trivial valid PNG
      const buf = fs.readFileSync(path.join('/input', id, 'image.png'));
      const px = decodePng(buf);
      const rep = represent(px);
      const filtered = applyFilters(rep.rows, rep.bpp, 'fixed0');
      const png = encodePng(rep, filtered);
      const outDir = path.join('/output', id);
      fs.mkdirSync(outDir, { recursive: true });
      fs.writeFileSync(path.join(outDir, 'image.png'), png);
      results.push({ id, type: rep.type, strat: 'fixed0-fallback', bytes: png.length, error: String(e && e.message || e) });
    }
  }
  for (const r of results) console.log(r.id + ' type=' + r.type + ' filter=' + r.strat + ' bytes=' + r.bytes + (r.error ? ' ERROR:' + r.error : ''));
}
main();
