import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const srcDir = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const dstDir = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";

// Per-opcode tables, indexed by opcode byte: immediate length, values
// popped, values pushed, and whether the byte is a real opcode at all.
const IMM = new Uint8Array(256);
IMM[1] = 1;
IMM[2] = 4;
IMM[48] = IMM[49] = IMM[50] = IMM[51] = 2;
const NEED = new Uint8Array(256);
const GIVE = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const op of [0, 1, 2, 3, 4, 5, 6, 7, 48, 49, 50, 51, 52, 64, 65, 80, 81, 82, 83]) KNOWN[op] = 1;
for (let op = 16; op <= 34; op++) {
  KNOWN[op] = 1;
  if (op === 23 || op === 27) {
    NEED[op] = 1;
    GIVE[op] = 1;
  } else {
    NEED[op] = 2;
    GIVE[op] = 1;
  }
}
NEED[3] = 1;
NEED[4] = 1;
GIVE[4] = 2;
NEED[5] = 2;
GIVE[5] = 2;
NEED[6] = 2;
GIVE[6] = 3;
NEED[7] = 3;
GIVE[7] = 3;
GIVE[1] = 1;
GIVE[2] = 1;
NEED[49] = 1;
NEED[50] = 1;
NEED[64] = 1;
GIVE[64] = 1;
NEED[65] = 2;
NEED[80] = 1;
NEED[81] = 1;
GIVE[82] = 1;
NEED[83] = 1;

// Runs one program on its input bytes; returns [stdout bytes, exit code].
// Every trap keeps the output written before it and exits with its code.
function solve(prog, feed) {
  const size = prog.length;
  const stack = new Int32Array(256);
  let top = 0;
  const calls = new Int32Array(64);
  let ctop = 0;
  const cells = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let blen = 0;
  let fpos = 0;
  let pc = 0;
  let done = 0;
  const finish = (code) => [buf.slice(0, blen), code];
  for (;;) {
    if (done === 1000000) return finish(10);
    if (pc < 0 || pc >= size) return finish(9);
    const op = prog[pc];
    if (!KNOWN[op]) return finish(5);
    const imm = IMM[op];
    if (pc + imm >= size) return finish(9);
    done++;
    const nxt = pc + 1 + imm;
    if (top < NEED[op]) return finish(2);
    if (top - NEED[op] + GIVE[op] > 256) return finish(3);
    pc = nxt;
    switch (op) {
      case 0x00:
        return finish(0);
      case 0x01:
        stack[top++] = (prog[nxt - 1] << 24) >> 24;
        break;
      case 0x02:
        stack[top++] = prog[nxt - 4] | (prog[nxt - 3] << 8) | (prog[nxt - 2] << 16) | (prog[nxt - 1] << 24);
        break;
      case 0x03:
        top--;
        break;
      case 0x04:
        stack[top] = stack[top - 1];
        top++;
        break;
      case 0x05: {
        const t = stack[top - 1];
        stack[top - 1] = stack[top - 2];
        stack[top - 2] = t;
        break;
      }
      case 0x06:
        stack[top] = stack[top - 2];
        top++;
        break;
      case 0x07: {
        const a = stack[top - 3];
        stack[top - 3] = stack[top - 2];
        stack[top - 2] = stack[top - 1];
        stack[top - 1] = a;
        break;
      }
      case 0x17:
        stack[top - 1] = -stack[top - 1] | 0;
        break;
      case 0x1b:
        stack[top - 1] = ~stack[top - 1];
        break;
      case 0x10:
      case 0x11:
      case 0x12:
      case 0x13:
      case 0x14:
      case 0x15:
      case 0x16:
      case 0x18:
      case 0x19:
      case 0x1a:
      case 0x1c:
      case 0x1d:
      case 0x1e:
      case 0x20:
      case 0x21:
      case 0x22: {
        const b = stack[top - 1];
        const a = stack[top - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return finish(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return finish(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return finish(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return finish(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        top -= 2;
        stack[top++] = r;
        break;
      }
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((prog[nxt - 2] | (prog[nxt - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = stack[--top];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nxt + rel;
        break;
      }
      case 0x33:
        if (ctop === 64) return finish(7);
        calls[ctop++] = nxt;
        pc = prog[nxt - 2] | (prog[nxt - 1] << 8);
        break;
      case 0x34:
        if (ctop === 0) return finish(8);
        pc = calls[--ctop];
        break;
      case 0x40: {
        const addr = stack[top - 1];
        if (addr < 0 || addr > 255) return finish(6);
        stack[top - 1] = cells[addr];
        break;
      }
      case 0x41: {
        const addr = stack[top - 1];
        const v = stack[top - 2];
        if (addr < 0 || addr > 255) return finish(6);
        top -= 2;
        cells[addr] = v;
        break;
      }
      case 0x50: {
        const text = String(stack[top - 1]);
        if (blen + text.length > 65536) return finish(11);
        top--;
        for (let i = 0; i < text.length; i++) buf[blen++] = text.charCodeAt(i);
        break;
      }
      case 0x51:
        if (blen + 1 > 65536) return finish(11);
        buf[blen++] = stack[--top] & 255;
        break;
      case 0x52:
        stack[top++] = fpos < feed.length ? feed[fpos++] : -1;
        break;
      case 0x53:
        return finish(stack[--top] & 255);
    }
  }
}

for (const id of readdirSync(srcDir).sort()) {
  const [out, code] = solve(readFileSync(join(srcDir, id, "program.bin")), readFileSync(join(srcDir, id, "input.bin")));
  mkdirSync(join(dstDir, id), { recursive: true });
  writeFileSync(join(dstDir, id, "stdout.bin"), out);
  writeFileSync(join(dstDir, id, "exit.txt"), code + "\n");
}
