var PadesJs = (function() {
'use strict';

var RESERVE_SIZE = 100000;
var RESERVE_SIZE_HEX = 200000;
var BYTE_RANGE_FMT = '/ByteRange [0 0000000000 0000000000 0000000000]';

function str2arr(str) {
    var arr = new Uint8Array(str.length);
    for (var i = 0; i < str.length; i++) arr[i] = str.charCodeAt(i);
    return arr;
}
function arr2str(arr, start, end) {
    start = start || 0;
    end = end || arr.length;
    var s = '';
    for (var i = start; i < end; i++) s += String.fromCharCode(arr[i]);
    return s;
}
function concatTypedArrays(a, b) {
    var c = new Uint8Array(a.length + b.length);
    c.set(a, 0);
    c.set(b, a.length);
    return c;
}
function b64toarr(b64) {
    var raw = atob(b64.replace(/\s/g, ''));
    return str2arr(raw);
}
function arr2b64(arr) {
    var s = '';
    for (var i = 0; i < arr.length; i++) s += String.fromCharCode(arr[i]);
    return btoa(s);
}
function bin2hex(arr) {
    var h = '';
    for (var i = 0; i < arr.length; i++) {
        h += ('0' + arr[i].toString(16)).slice(-2);
    }
    return h.toUpperCase();
}
function strToWin1251Literal(s) {
    var bytes = [];
    for (var i = 0; i < s.length; i++) {
        var c = s.charCodeAt(i);
        if (c === 0x0401) bytes.push(0xA8);
        else if (c === 0x0451) bytes.push(0xB8);
        else if (c >= 0x0410 && c <= 0x044F) bytes.push(c - 0x0410 + 0xC0);
        else bytes.push(c < 256 ? c : 0x3F);
    }
    var out = '(';
    for (var j = 0; j < bytes.length; j++) {
        var b = bytes[j];
        if (b < 0x20 || b > 0x7E) out += '\\' + ('000' + b.toString(8)).slice(-3);
        else if (b === 0x28 || b === 0x29 || b === 0x5C) out += '\\' + String.fromCharCode(b);
        else out += String.fromCharCode(b);
    }
    out += ')';
    return out;
}
function isWs(b) { return b === 0x20 || b === 0x0a || b === 0x0d || b === 0x09; }
function skipWs(arr, p) { while (p < arr.length && isWs(arr[p])) p++; return p; }
function isDelim(b) { return b === 0x28 || b === 0x29 || b === 0x3c || b === 0x3e || b === 0x5b || b === 0x5d || b === 0x7b || b === 0x7d || b === 0x2f || b === 0x25; }

// ── PdfReader ──────────────────────────────────────
function PdfReader(bytes) {
    if (typeof bytes === 'string') this.data = str2arr(bytes);
    else this.data = bytes;
    this.xref = {};
    this.trailer = {};
    this._parse();
}
PdfReader.prototype._parse = function() {
    var xrOff = this._findStartXref();
    this._parseChain(xrOff, true);
};
PdfReader.prototype._findStartXref = function() {
    var data = this.data;
    var needle = str2arr('startxref');
    var last = -1;
    for (var i = data.length - needle.length; i >= 0; i--) {
        var ok = true;
        for (var j = 0; j < needle.length; j++) {
            if (data[i + j] !== needle[j]) { ok = false; break; }
        }
        if (ok) { last = i; break; }
    }
    if (last < 0) throw new Error('startxref not found');
    var p = last + 9;
    p = skipWs(data, p);
    var num = '';
    while (p < data.length && data[p] >= 0x30 && data[p] <= 0x39) {
        num += String.fromCharCode(data[p++]);
    }
    return parseInt(num, 10);
};
PdfReader.prototype._parseChain = function(pos, isTop) {
    var d = this.data, len = d.length;
    var p = pos;
    var xrefFound = false;
    if (d[p] === 0x78 && d[p+1] === 0x72 && d[p+2] === 0x65 && d[p+3] === 0x66) {
        this._parseXrefEntries(p);
        xrefFound = true;
    } else {
        for (var s = Math.max(0, pos - 25); s < Math.min(len, pos + 30); s++) {
            if (d[s]===0x78 && d[s+1]===0x72 && d[s+2]===0x65 && d[s+3]===0x66) {
                this._parseXrefEntries(s);
                xrefFound = true;
                break;
            }
        }
    }
    var trStart = -1;
    for (var i = p; i < len - 6; i++) {
        if (d[i]===0x74 && d[i+1]===0x72 && d[i+2]===0x61 && d[i+3]===0x69 && d[i+4]===0x6c && d[i+5]===0x65 && d[i+6]===0x72) {
            trStart = i; break;
        }
    }
    if (trStart >= 0) {
        var trEnd = -1;
        for (var j = trStart; j < len - 9; j++) {
            if (d[j]===0x73 && d[j+1]===0x74 && d[j+2]===0x61 && d[j+3]===0x72 && d[j+4]===0x74 && d[j+5]===0x78 && d[j+6]===0x72 && d[j+7]===0x65 && d[j+8]===0x66) {
                trEnd = j; break;
            }
        }
        if (trEnd < 0) {
            for (var k = trStart; k < len - 4; k++) {
                if (d[k]===0x25 && d[k+1]===0x25 && d[k+2]===0x45 && d[k+3]===0x4f && d[k+4]===0x46) {
                    trEnd = k; break;
                }
            }
        }
        if (trEnd < 0) trEnd = len;
        var trStr = arr2str(d, trStart + 7, trEnd).trim();
        var tr = this._parseDict(trStr);
        if (isTop || Object.keys(this.trailer).length === 0) this.trailer = tr;
        if (tr.Prev && parseInt(tr.Prev) > 0) this._parseChain(parseInt(tr.Prev), false);
    }
};
PdfReader.prototype._parseXrefEntries = function(pos) {
    var d = this.data, len = d.length;
    var p = pos + 4;
    p = skipWs(d, p);
    while (p < len) {
        if (d[p]===0x74 && d[p+1]===0x72 && d[p+2]===0x61 && d[p+3]===0x69 && d[p+4]===0x6c && d[p+5]===0x65 && d[p+6]===0x72) break;
        var line = '';
        while (p < len && d[p] !== 0x0a && d[p] !== 0x0d) line += String.fromCharCode(d[p++]);
        if (d[p] === 0x0d) p++;
        if (d[p] === 0x0a) p++;
        line = line.trim();
        if (!line) continue;
        var m = line.match(/^(\d+)\s+(\d+)$/);
        if (!m) break;
        var startNum = parseInt(m[1]), count = parseInt(m[2]);
        for (var i = 0; i < count; i++) {
            if (p + 20 > len) break;
            var entry = arr2str(d, p, p + 20);
            p += 20;
            if (d[p] === 0x0d) p++;
            if (d[p] === 0x0a) p++;
            var offset = parseInt(entry.substr(0, 10));
            var inUse = entry.substr(17, 1).trim();
            if (inUse === 'n' && !(startNum + i in this.xref)) {
                this.xref[startNum + i] = offset;
            }
        }
    }
};
PdfReader.prototype.getObjectRaw = function(objNum) {
    var offset = this.xref[objNum];
    if (offset === undefined) throw new Error('Object ' + objNum + ' 0 R not found in xref');
    var d = this.data, len = d.length, cursor = offset;
    var objPos = -1;
    for (var i = cursor; i < Math.min(len, cursor + 50); i++) {
        if (d[i]===0x6f && d[i+1]===0x62 && d[i+2]===0x6a) { objPos = i; break; }
    }
    if (objPos < 0) throw new Error('Cannot find obj keyword at offset ' + offset);
    var cStart = objPos + 3;
    cStart = skipWs(d, cStart);
    var depth = 0, inStream = false, streamLen = 0;
    cursor = cStart;
    while (cursor < len) {
        if (!inStream && d[cursor]===0x73 && d[cursor+1]===0x74 && d[cursor+2]===0x72 && d[cursor+3]===0x65 && d[cursor+4]===0x61 && d[cursor+5]===0x6d) {
            var dlStr = arr2str(d, cStart, cursor).trim();
            var sdl = this._parseDict(dlStr);
            streamLen = parseInt(sdl.Length) || 0;
            inStream = true;
            cursor += 6;
            if (d[cursor] === 0x0d) cursor++;
            if (d[cursor] === 0x0a) cursor++;
            cursor += streamLen;
            continue;
        }
        if (inStream && d[cursor]===0x65 && d[cursor+1]===0x6e && d[cursor+2]===0x64 && d[cursor+3]===0x73 && d[cursor+4]===0x74 && d[cursor+5]===0x72 && d[cursor+6]===0x65 && d[cursor+7]===0x61 && d[cursor+8]===0x6d) {
            inStream = false; cursor += 9; continue;
        }
        if (d[cursor]===0x65 && d[cursor+1]===0x6e && d[cursor+2]===0x64 && d[cursor+3]===0x6f && d[cursor+4]===0x62 && d[cursor+5]===0x6a) {
            if (depth <= 0) return arr2str(d, cStart, cursor);
            depth--; cursor += 6; continue;
        }
        if (d[cursor]===0x3c && d[cursor+1]===0x3c) { depth++; cursor += 2; continue; }
        if (d[cursor]===0x3e && d[cursor+1]===0x3e) { depth--; cursor += 2; continue; }
        cursor++;
    }
    throw new Error('Cannot find endobj for object ' + objNum);
};
PdfReader.prototype.getObject = function(objNum) {
    var raw = this.getObjectRaw(objNum);
    var sp = raw.indexOf('stream');
    if (sp >= 0) raw = raw.substring(0, sp);
    return raw.trim();
};
PdfReader.prototype._parseDict = function(str) {
    var result = {};
    var tokens = this._tokenize(str);
    var i = 0;
    while (i < tokens.length - 1) {
        var key = tokens[i];
        if (key[0] === '/') {
            var next = tokens[i + 1];
            if (next === '<<') {
                var j = i + 2, depth = 1;
                while (j < tokens.length && depth > 0) {
                    if (tokens[j] === '<<') depth++;
                    else if (tokens[j] === '>>') depth--;
                    j++;
                }
                var inner = tokens.slice(i + 2, j - 1);
                next = this._parseDictFromTokens(inner);
                result[key.substring(1)] = next;
                i = j; continue;
            } else if (next === '[') {
                var k = i + 2, depth2 = 1;
                while (k < tokens.length && depth2 > 0) {
                    if (tokens[k] === '[') depth2++;
                    else if (tokens[k] === ']') depth2--;
                    k++;
                }
                var inner2 = tokens.slice(i + 2, k - 1);
                next = this._parseArrayFromTokens(inner2);
                result[key.substring(1)] = next;
                i = k; continue;
            } else {
                result[key.substring(1)] = next;
                i += 2; continue;
            }
        }
        i++;
    }
    return result;
};
PdfReader.prototype._parseDictFromTokens = function(tokens) {
    var result = {}, i = 0;
    while (i < tokens.length - 1) {
        var key = tokens[i];
        if (key[0] === '/') {
            var next = tokens[i + 1];
            if (next === '<<') {
                var j = i + 2, depth = 1;
                while (j < tokens.length && depth > 0) {
                    if (tokens[j] === '<<') depth++;
                    else if (tokens[j] === '>>') depth--;
                    j++;
                }
                var inner = tokens.slice(i + 2, j - 1);
                next = this._parseDictFromTokens(inner);
                result[key.substring(1)] = next;
                i = j; continue;
            } else if (next === '[') {
                var k = i + 2, depth2 = 1;
                while (k < tokens.length && depth2 > 0) {
                    if (tokens[k] === '[') depth2++;
                    else if (tokens[k] === ']') depth2--;
                    k++;
                }
                var inner2 = tokens.slice(i + 2, k - 1);
                next = this._parseArrayFromTokens(inner2);
                result[key.substring(1)] = next;
                i = k; continue;
            } else {
                result[key.substring(1)] = next;
                i += 2; continue;
            }
        }
        i++;
    }
    return result;
};
PdfReader.prototype._parseArrayFromTokens = function(tokens) {
    var result = [], i = 0;
    while (i < tokens.length) {
        var t = tokens[i];
        if (t === '<<') {
            var j = i + 1, depth = 1;
            while (j < tokens.length && depth > 0) {
                if (tokens[j] === '<<') depth++;
                else if (tokens[j] === '>>') depth--;
                j++;
            }
            var inner = tokens.slice(i + 1, j - 1);
            result.push(this._parseDictFromTokens(inner));
            i = j; continue;
        } else if (t === '[') {
            var k = i + 1, depth2 = 1;
            while (k < tokens.length && depth2 > 0) {
                if (tokens[k] === '[') depth2++;
                else if (tokens[k] === ']') depth2--;
                k++;
            }
            var inner2 = tokens.slice(i + 1, k - 1);
            result.push(this._parseArrayFromTokens(inner2));
            i = k; continue;
        } else {
            result.push(t);
            i++;
        }
    }
    return result;
};
PdfReader.prototype._tokenize = function(str) {
    var tokens = [];
    var i = 0, len = str.length;
    while (i < len) {
        var ch = str[i];
        if (ch === ' ' || ch === '\n' || ch === '\r' || ch === '\t') { i++; continue; }
        if (ch === '%') { while (i < len && str[i] !== '\n' && str[i] !== '\r') i++; continue; }
        if (ch === '<' && str[i+1] === '<') { tokens.push('<<'); i += 2; continue; }
        if (ch === '>' && str[i+1] === '>') { tokens.push('>>'); i += 2; continue; }
        if (ch === '[') { tokens.push('['); i++; continue; }
        if (ch === ']') { tokens.push(']'); i++; continue; }
        if (ch === '<') { var h = i; i++; while (i < len && str[i] !== '>') i++; if (i < len) i++; tokens.push(str.substring(h, i)); continue; }
        if (ch === '(') { var start = i, d = 1; i++; while (i < len && d > 0) { if (str[i] === '\\') i += 2; else { if (str[i] === '(') d++; if (str[i] === ')') d--; i++; } } tokens.push(str.substring(start, i)); continue; }
        if (ch === '/') { var s = i; i++; while (i < len && str[i] !== ' ' && str[i] !== '\n' && str[i] !== '\r' && str[i] !== '\t' && str[i] !== '(' && str[i] !== ')' && str[i] !== '<' && str[i] !== '>' && str[i] !== '[' && str[i] !== ']' && str[i] !== '/' && str[i] !== '%') i++; tokens.push(str.substring(s, i)); continue; }
        if (ch === '-' || ch === '+' || (ch >= '0' && ch <= '9') || ch === '.') { var a = i; i++; while (i < len && ((str[i] >= '0' && str[i] <= '9') || str[i] === '.')) i++; var after = str.substring(i); var rm = after.match(/^\s+0\s+R\b/); if (rm) { tokens.push(str.substring(a, i) + ' 0 R'); i += rm[0].length; } else tokens.push(str.substring(a, i)); continue; }
        tokens.push(ch);
        i++;
    }
    return tokens;
};
PdfReader.prototype.parseRef = function(ref) {
    var m = ref.trim().match(/^(\d+)\s+0\s+R$/);
    if (!m) throw new Error('Cannot parse ref: ' + ref);
    return parseInt(m[1]);
};
PdfReader.prototype.serializeRef = function(n) { return n + ' 0 R'; };
PdfReader.prototype.getMaxObjNum = function() {
    return Math.max.apply(null, Object.keys(this.xref).map(Number));
};
PdfReader.prototype.getTrailer = function() { return this.trailer; };
PdfReader.prototype.getRootCatalog = function() {
    var rootRef = this.trailer.Root;
    if (!rootRef) throw new Error('No /Root in trailer');
    return this._parseDict(this.getObject(this.parseRef(rootRef)));
};
PdfReader.prototype.getPagesTree = function() {
    var cat = this.getRootCatalog();
    return this._readPagesTree(cat.Pages);
};
PdfReader.prototype._readPagesTree = function(pagesRef) {
    var num = this.parseRef(pagesRef);
    var dict = this._parseDict(this.getObject(num));
    var kidsRaw = dict.Kids;
    if (!Array.isArray(kidsRaw)) kidsRaw = [kidsRaw];
    var kids = [];
    for (var i = 0; i < kidsRaw.length; i++) {
        var ref = kidsRaw[i];
        var kn = this.parseRef(ref);
        var kd = this._parseDict(this.getObject(kn));
        if (kd.Type === '/Pages') {
            kids = kids.concat(this._readPagesTree(ref).kids);
        } else {
            kids.push({ ref: ref, objNum: kn, dict: kd });
        }
    }
    return { ref: pagesRef, objNum: num, dict: dict, kids: kids };
};
PdfReader.prototype.getFirstPageRef = function() {
    var pt = this.getPagesTree();
    if (!pt.kids.length) throw new Error('No pages found');
    return pt.kids[0].ref;
};
PdfReader.prototype.getFirstPageDict = function() {
    var pt = this.getPagesTree();
    if (!pt.kids.length) throw new Error('No pages found');
    return pt.kids[0].dict;
};

// ── PdfWriter ──────────────────────────────────────
function PdfWriter() {}
PdfWriter.prototype.buildIncrementalUpdate = function(origBytes, newObjects, newSize, rootObjNum, oldXrefOffset) {
    var baseLen = (typeof origBytes === 'string') ? origBytes.length : origBytes.byteLength;
    var inc = '';
    var offsets = {};
    var keys = Object.keys(newObjects).map(Number).sort(function(a,b){return a-b;});
    for (var ki = 0; ki < keys.length; ki++) {
        var num = keys[ki];
        offsets[num] = inc.length;
        inc += num + ' 0 obj\n' + newObjects[num] + '\nendobj\n';
    }
    var xref = 'xref\n0 1\n' + padOffset(0) + ' 65535 f \n';
    var groups = [];
    for (var gi = 0; gi < keys.length; gi++) {
        var n = keys[gi];
        if (groups.length === 0 || n !== groups[groups.length-1].start + groups[groups.length-1].count) {
            groups.push({ start: n, count: 1 });
        } else {
            groups[groups.length-1].count++;
        }
    }
    for (var gj = 0; gj < groups.length; gj++) {
        var g = groups[gj];
        xref += g.start + ' ' + g.count + '\n';
        for (var gn = 0; gn < g.count; gn++) {
            var objNum = g.start + gn;
            xref += padOffset(baseLen + offsets[objNum], true) + ' 00000 n \n';
        }
    }
    var prev = oldXrefOffset > 0 ? ' /Prev ' + oldXrefOffset : '';
    var trailer = 'trailer\n<</Size ' + newSize + '/Root ' + rootObjNum + ' 0 R' + prev + '>>\n';
    var totalSoFar = inc + xref + trailer;
    var xrefOff = baseLen + inc.length;
    totalSoFar += 'startxref\n' + xrefOff + '\n%%EOF\n';
    return { bytes: totalSoFar, newXrefOffset: xrefOff };
};

function padOffset(num) {
    var s = '' + num;
    while (s.length < 10) s = '0' + s;
    return s;
}
PdfWriter.serializeDict = function(dict) {
    var parts = [];
    var keys = Object.keys(dict);
    for (var i = 0; i < keys.length; i++) {
        parts.push('/' + keys[i] + ' ' + PdfWriter.serializeValue(dict[keys[i]]));
    }
    return '<<' + parts.join(' ') + '>>';
};
PdfWriter.serializeValue = function(val) {
    if (typeof val === 'string') {
        if (/^\d+ 0 R$/.test(val)) return val;
        if (val[0] === '/') return val;
        if (val[0] === '<' && val[val.length-1] === '>') return val;
        if (val[0] === '(' && val[val.length-1] === ')') return val;
        if (val === 'true' || val === 'false' || val === 'null') return val;
        if (/^[+\-]?\d+(\.\d+)?$/.test(val)) return val;
        return '(' + PdfWriter.escapeLiteral(val) + ')';
    }
    if (typeof val === 'number') return '' + val;
    if (typeof val === 'boolean') return val ? 'true' : 'false';
    if (Array.isArray(val)) return PdfWriter.serializeArray(val);
    if (val && typeof val === 'object') return PdfWriter.serializeDict(val);
    return '' + val;
};
PdfWriter.serializeArray = function(arr) {
    var parts = [];
    for (var i = 0; i < arr.length; i++) parts.push(PdfWriter.serializeValue(arr[i]));
    return '[' + parts.join(' ') + ']';
};
PdfWriter.escapeLiteral = function(s) {
    return s.replace(/\\/g, '\\\\').replace(/\(/g, '\\(').replace(/\)/g, '\\)');
};
PdfWriter.encodePdfString = function(utf8) {
    try {
        var enc = new TextEncoder();
        var utf16 = new Uint8Array(enc.encode(utf8));
        return '<FEFF' + bin2hex(utf16) + '>';
    } catch(e) {
        return '<>';
    }
};
PdfWriter.serializeStream = function(dict, content) {
    var header = PdfWriter.serializeDict(dict);
    return header + '\nstream\n' + content + '\nendstream';
};

// ── ByteRangeCalculator ────────────────────────────
function ByteRangeCalculator() {}
ByteRangeCalculator.prototype.locateAndFill = function(pdf) {
    var len = pdf.length, data = pdf;
    var brPos = data.indexOf('/ByteRange');
    if (brPos < 0) throw new Error('/ByteRange not found');
    var bStart = data.indexOf('[', brPos);
    var bEnd = data.indexOf(']', bStart);
    if (bStart < 0 || bEnd < 0) throw new Error('Cannot find [] for ByteRange');
    var csPos = data.indexOf('/Contents', brPos);
    if (csPos < 0) throw new Error('/Contents not found after ByteRange');
    var hStart = data.indexOf('<', csPos);
    var hEnd = data.indexOf('>', hStart);
    if (hStart < 0 || hEnd < 0) throw new Error('Cannot find <> for Contents');
    hEnd++;
    var br1 = hStart;
    var br2 = hEnd;
    var br3 = len - hEnd;
    var newBr = '/ByteRange [0 ' + ('         ' + br1).slice(-10) + ' ' + ('         ' + br2).slice(-10) + ' ' + ('         ' + br3).slice(-10) + ']';
    var oldLen = bEnd - brPos + 1;
    if (newBr.length !== oldLen) {
        var diff = oldLen - newBr.length;
        if (diff > 0) {
            var insPos = newBr.lastIndexOf(']');
            newBr = newBr.substring(0, insPos) + new Array(diff + 1).join(' ') + ']';
        }
    }
    pdf = pdf.substring(0, brPos) + newBr + pdf.substring(brPos + oldLen);
    return {
        pdf: pdf,
        contentsHexStart: hStart + 1,
        contentsEnd: hEnd,
        byteRange: [0, br1, br2, br3]
    };
};
ByteRangeCalculator.prototype.extractSignedBytes = function(pdf, br) {
    return pdf.substring(br[0], br[1]) + pdf.substring(br[2]);
};
ByteRangeCalculator.prototype.injectSignature = function(pdf, hexStart, cadesHex) {
    var hl = cadesHex.length;
    if (hl < RESERVE_SIZE_HEX) {
        cadesHex += new Array(RESERVE_SIZE_HEX - hl + 1).join('0');
    }
    return pdf.substring(0, hexStart) + cadesHex + pdf.substring(hexStart + RESERVE_SIZE_HEX);
};

// ── PadesEmbedder ──────────────────────────────────
function PadesEmbedder() {
    this.brCalc = new ByteRangeCalculator();
}

PadesEmbedder.prototype._getPageBox = function(pageDict) {
    var box = pageDict.MediaBox || pageDict.CropBox;
    if (!box || !Array.isArray(box) || box.length < 4) return [595, 842];
    return [parseFloat(box[2]) || 595, parseFloat(box[3]) || 842];
};

PadesEmbedder.prototype._formatPdfDate = function(d) {
    d = d || new Date();
    var pad = function(n) { return ('0' + n).slice(-2); };
    var y = d.getUTCFullYear();
    var m = pad(d.getUTCMonth() + 1);
    var day = pad(d.getUTCDate());
    var h = pad(d.getUTCHours());
    var min = pad(d.getUTCMinutes());
    var s = pad(d.getUTCSeconds());
    var tzOff = -d.getTimezoneOffset();
    var tzH = pad(Math.floor(Math.abs(tzOff) / 60));
    var tzM = pad(Math.abs(tzOff) % 60);
    var tzSign = tzOff >= 0 ? '+' : '-';
    return 'D:' + y + m + day + h + min + s + tzSign + tzH + "'" + tzM + "'";
};

PadesEmbedder.prototype._buildCyrillicFontDict = function() {
    var diffs = [168, '/afii10023', 184, '/afii10071', 192];
    var up = ['afii10017','afii10018','afii10019','afii10020','afii10021','afii10022',
              'afii10024','afii10025','afii10026','afii10027','afii10028','afii10029',
              'afii10030','afii10031','afii10032','afii10033','afii10034','afii10035',
              'afii10036','afii10037','afii10038','afii10039','afii10040','afii10041',
              'afii10042','afii10043','afii10044','afii10045','afii10046','afii10047',
              'afii10048','afii10049'];
    for (var i = 0; i < up.length; i++) diffs.push('/' + up[i]);
    diffs.push(224);
    var lo = ['afii10065','afii10066','afii10067','afii10068','afii10069','afii10070',
              'afii10072','afii10073','afii10074','afii10075','afii10076','afii10077',
              'afii10078','afii10079','afii10080','afii10081','afii10082','afii10083',
              'afii10084','afii10085','afii10086','afii10087','afii10088','afii10089',
              'afii10090','afii10091','afii10092','afii10093','afii10094','afii10095',
              'afii10096','afii10097'];
    for (var j = 0; j < lo.length; j++) diffs.push('/' + lo[j]);

    var widths = [
      278,278,355,556,556,889,667,191,333,333,389,584,278,333,278,278,
      556,556,556,556,556,556,556,556,556,556,278,278,584,584,584,556,
      1015,667,667,722,722,667,611,778,722,278,500,667,556,833,722,778,
      667,778,722,667,611,722,667,944,667,667,611,278,278,278,469,556,
      222,556,556,500,556,556,278,556,556,222,222,500,222,833,556,556,
      556,556,333,500,278,556,500,722,500,500,500,334,260,334,584,350,
      500,500,500,500,500,500,500,500,500,500,500,500,500,500,500,500,
      500,500,500,500,500,500,500,500,500,500,500,500,500,500,500,500,
      278,500,500,500,500,500,500,500,500,500,667,500,500,500,500,500,
      500,500,500,500,500,500,500,500,500,500,500,500,500,500,500,500,
      667,667,667,556,722,667,944,611,722,722,667,722,833,722,778,722,
      667,722,611,667,778,667,722,667,944,944,778,833,667,722,944,667,
      556,556,500,389,556,556,722,500,556,556,500,556,722,556,556,556,
      556,500,500,556,722,500,556,556,833,833,611,722,556,556,778,556
    ];
    widths[168 - 32] = 667;
    widths[184 - 32] = 556;

    return {
        Type: '/Font',
        Subtype: '/Type1',
        BaseFont: '/Helvetica',
        FirstChar: 32,
        LastChar: 255,
        Widths: widths,
        Encoding: {
            Type: '/Encoding',
            BaseEncoding: '/WinAnsiEncoding',
            Differences: diffs
        }
    };
};

PadesEmbedder.prototype._parseJpegSize = function(bytes) {
    if (!bytes || bytes.length < 4 || bytes[0] !== 0xFF || bytes[1] !== 0xD8) return null;
    var i = 2;
    while (i < bytes.length - 8) {
        if (bytes[i] !== 0xFF) return null;
        var m = bytes[i + 1];
        if (m >= 0xC0 && m <= 0xCF && m !== 0xC4 && m !== 0xC8 && m !== 0xCC) {
            return { width: (bytes[i + 7] << 8) | bytes[i + 8], height: (bytes[i + 5] << 8) | bytes[i + 6] };
        }
        var len = (bytes[i + 2] << 8) | bytes[i + 3];
        if (len < 2) return null;
        i += 2 + len;
    }
    return null;
};

PadesEmbedder.prototype._buildImageXObject = function(bytes, w, h) {
    var s = '';
    for (var i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
    return '<</Type /XObject /Subtype /Image /Width ' + w + ' /Height ' + h +
        ' /ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length ' + bytes.length + '>>\nstream\n' + s + '\nendstream';
};

PadesEmbedder.prototype._formatCertSerial = function(s) {
    if (!s) return '';
    var clean = String(s).replace(/\s+/g, '').toUpperCase();
    if (clean.length > 32) clean = clean.substring(clean.length - 32);
    return clean;
};

PadesEmbedder.prototype._fmtDate = function(d) {
    if (!d) return '';
    var dt = (d instanceof Date) ? d : new Date(d);
    if (isNaN(dt.getTime())) return String(d);
    var pad = function(n) { return ('0' + n).slice(-2); };
    return pad(dt.getDate()) + '.' + pad(dt.getMonth() + 1) + '.' + dt.getFullYear();
};

PadesEmbedder.prototype._formatValidity = function(from, to) {
    var f = this._fmtDate(from), t = this._fmtDate(to);
    if (!f && !t) return '—';
    return 'с ' + (f || '—') + ' по ' + (t || '—');
};

PadesEmbedder.prototype._buildAppearanceXObject = function(w, h, info, logo) {
    var fontRes = { 'Fx1': this._buildCyrillicFontDict() };
    var fk = '/Fx1';
    var bx = Math.round(w), bh = Math.round(h);
    var pad = 6;

    var topH = 32;
    var topY = bh - topH;

    var logoArea = null;
    var titleX = pad;
    if (logo && logo.w > 0 && logo.h > 0) {
        var maxW = 41.0, maxH = topH - 2;
        var r = Math.min(maxW / logo.w, maxH / logo.h);
        var dw = logo.w * r, dh = logo.h * r;
        logoArea = { x: pad, y: topY + (topH - dh) / 2 - bh * 0.03, w: dw, h: dh };
        titleX = Math.round(logoArea.x + logoArea.w + 8);
    }

    var c = 'q\n';
    var cr = 8, ck = cr * 0.5522847498;
    var bx0 = 0.5, by0 = 0.5, bx1 = bx - 0.5, by1 = bh - 0.5;
    c += '1 1 1 rg\n';
    c += '0 0 0 RG 1.2 w\n';
    c += (cr + bx0).toFixed(1) + ' ' + by0.toFixed(1) + ' m\n';
    c += (bx1 - cr).toFixed(1) + ' ' + by0.toFixed(1) + ' l\n';
    c += (bx1 - cr + ck).toFixed(2) + ' ' + by0.toFixed(1) + ' ' + bx1.toFixed(1) + ' ' + (cr - ck).toFixed(2) + ' ' + bx1.toFixed(1) + ' ' + (cr + by0).toFixed(1) + ' c\n';
    c += bx1.toFixed(1) + ' ' + (by1 - cr).toFixed(1) + ' l\n';
    c += bx1.toFixed(1) + ' ' + (by1 - cr + ck).toFixed(2) + ' ' + (bx1 - cr + ck).toFixed(2) + ' ' + by1.toFixed(1) + ' ' + (bx1 - cr).toFixed(1) + ' ' + by1.toFixed(1) + ' c\n';
    c += (cr + bx0).toFixed(1) + ' ' + by1.toFixed(1) + ' l\n';
    c += (cr - ck).toFixed(2) + ' ' + by1.toFixed(1) + ' ' + bx0.toFixed(1) + ' ' + (by1 - cr + ck).toFixed(2) + ' ' + bx0.toFixed(1) + ' ' + (by1 - cr).toFixed(1) + ' c\n';
    c += bx0.toFixed(1) + ' ' + (cr + by0).toFixed(1) + ' l\n';
    c += bx0.toFixed(1) + ' ' + (cr - ck).toFixed(2) + ' ' + (cr - ck).toFixed(2) + ' ' + by0.toFixed(1) + ' ' + (cr + bx0).toFixed(1) + ' ' + by0.toFixed(1) + ' c\n';
    c += 'B\n';

    if (logoArea) {
        c += 'q\n' + logoArea.w.toFixed(2) + ' 0 0 ' + logoArea.h.toFixed(2) +
             ' ' + logoArea.x.toFixed(2) + ' ' + logoArea.y.toFixed(2) +
             ' cm\n/Im1 Do\nQ\n';
    }

    var t1 = 'ДОКУМЕНТ ПОДПИСАН';
    var t2 = 'ЭЛЕКТРОННОЙ ПОДПИСЬЮ';
    c += 'BT\n' + fk + ' 9.0 Tf\n0 0 0 rg\n0 0 0 RG 0.3 w 2 Tr\n' +
         titleX + ' ' + (bh - 17) + ' Td\n' +
         strToWin1251Literal(t1) + ' Tj\nET\n';
    c += 'BT\n' + fk + ' 9.0 Tf\n0 0 0 rg\n0 0 0 RG 0.3 w 2 Tr\n' +
         titleX + ' ' + (bh - 28) + ' Td\n' +
         strToWin1251Literal(t2) + ' Tj\nET\n';
    c += 'BT\n0 Tr\nET\n';

    var serial = info.certSerial ? this._formatCertSerial(info.certSerial) : '';
    var lines = [
        ['Сертификат: ',   serial || '—'],
        ['Владелец: ',     info.signerName || '—'],
        ['Действителен: ', this._formatValidity(info.validFrom, info.validTo)]
    ];

    var infoFontSize = 7.8;
    var step = 12.8;
    var firstLineY = topY - 13.8;

    for (var i = 0; i < lines.length; i++) {
        c += 'BT\n' + fk + ' ' + infoFontSize + ' Tf\n0 0 0 rg\n' +
             pad + ' ' + (firstLineY - i * step) + ' Td\n' +
             strToWin1251Literal(lines[i][0] + lines[i][1]) + ' Tj\nET\n';
    }
    c += 'Q\n';

    var resources = { Font: fontRes };
    if (logo && logo.ref) resources.XObject = { 'Im1': logo.ref };

    var dict = {
        Type: '/XObject', Subtype: '/Form', FormType: 1,
        BBox: [0, 0, w, h],
        Resources: resources,
        Length: c.length
    };
    return PdfWriter.serializeStream(dict, c);
};

PadesEmbedder.prototype.prepareForSigning = function(pdfBytes, signerName, opts) {
    signerName = signerName || '';
    opts = opts || {};
    var logoBytes = opts.logoBytes || null;
    var certInfo = {
        signerName: signerName,
        certSerial: opts.certSerial || '',
        validFrom:  opts.validFrom  || null,
        validTo:    opts.validTo    || null
    };

    var reader = new PdfReader(pdfBytes);
    var maxNum = reader.getMaxObjNum();
    var rootNum = reader.parseRef(reader.getTrailer().Root);
    var firstPage = reader.getPagesTree().kids[0];
    var firstPageNum = firstPage.objNum;
    var oldXrOff = reader._findStartXref();

    var aNum = maxNum + 1, fNum = maxNum + 2, sNum = maxNum + 3, xNum = maxNum + 4;
    var imgNum = 0, newSize = maxNum + 5, logoInfo = null;
    if (logoBytes && logoBytes.length) {
        var sz = this._parseJpegSize(logoBytes);
        if (sz) {
            imgNum = maxNum + 5;
            newSize = maxNum + 6;
            logoInfo = { w: sz.width, h: sz.height, ref: reader.serializeRef(imgNum) };
        }
    }

    var origCat = reader.getRootCatalog();
    var origPg  = reader.getFirstPageDict();

    var pageBox = this._getPageBox(origPg);
    var pw = pageBox[0];
    var ph = pageBox[1];

    var sigW = Math.min(pw - 80, 204);
    var sigH = 78;
    var sigX1 = (typeof opts.stampX === 'number' && isFinite(opts.stampX)) ? opts.stampX : 40;
    var sigY1 = (typeof opts.stampY === 'number' && isFinite(opts.stampY)) ? opts.stampY : 40;
    if (sigX1 < 0) sigX1 = 0;
    if (sigX1 + sigW > pw) sigX1 = Math.max(0, pw - sigW);
    if (sigY1 < 0) sigY1 = 0;
    if (sigY1 + sigH > ph) sigY1 = Math.max(0, ph - sigH);
    var sigX2 = sigX1 + sigW, sigY2 = sigY1 + sigH;

    var newObjs = {};
    newObjs[aNum] = PdfWriter.serializeDict({ Fields: [reader.serializeRef(fNum)], SigFlags: 3 });
    newObjs[fNum] = PdfWriter.serializeDict({
        Type: '/Annot', Subtype: '/Widget', FT: '/Sig',
        Rect: [sigX1, sigY1, sigX2, sigY2],
        AP: { N: reader.serializeRef(xNum) },
        T: 'Signature1',
        V: reader.serializeRef(sNum),
        P: reader.serializeRef(firstPageNum),
        F: 132
    });

    var parts = ['/Type /Sig', '/Filter /Adobe.PPKLite', '/SubFilter /ETSI.CAdES.detached'];
    if (signerName) parts.push('/Name ' + PdfWriter.encodePdfString(signerName));
    parts.push(BYTE_RANGE_FMT);
    parts.push('/Contents <' + new Array(RESERVE_SIZE_HEX + 1).join('0') + '>');
    parts.push('/M (' + this._formatPdfDate() + ')');
    newObjs[sNum] = '<<\n' + parts.join('\n') + '\n>>';

    newObjs[xNum] = this._buildAppearanceXObject(sigW, sigH, certInfo, logoInfo);
    if (imgNum) newObjs[imgNum] = this._buildImageXObject(logoBytes, logoInfo.w, logoInfo.h);

    var nc = {};
    for (var k in origCat) nc[k] = origCat[k];
    nc.AcroForm = reader.serializeRef(aNum);
    newObjs[rootNum] = PdfWriter.serializeDict(nc);

    var np = {};
    for (var p1 in origPg) np[p1] = origPg[p1];
    var an = origPg.Annots, annots = [];
    if (an) annots = Array.isArray(an) ? an.slice() : [an];
    annots.push(reader.serializeRef(fNum));
    np.Annots = annots;
    newObjs[firstPageNum] = PdfWriter.serializeDict(np);

    var writer = new PdfWriter();
    var upd = writer.buildIncrementalUpdate(pdfBytes, newObjs, newSize, rootNum, oldXrOff);
    var full = pdfBytes + upd.bytes;

    var loc = this.brCalc.locateAndFill(full);
    var dataToSign = this.brCalc.extractSignedBytes(loc.pdf, loc.byteRange);

    return { dataToSign: dataToSign, state: loc };
};
PadesEmbedder.prototype.finalizeSignature = function(state, sigRaw) {
    var pdf = state.pdf;
    if (typeof sigRaw === 'string') sigRaw = b64toarr(sigRaw);
    var cadesHex = bin2hex(sigRaw);
    return this.brCalc.injectSignature(pdf, state.contentsHexStart, cadesHex);
};

return {
    PdfReader: PdfReader,
    PdfWriter: PdfWriter,
    ByteRangeCalculator: ByteRangeCalculator,
    PadesEmbedder: PadesEmbedder,
    RESERVE_SIZE_HEX: RESERVE_SIZE_HEX
};
})();