// Tiny stack VM, candidate A: a faithful switch interpreter of make.fun's tiny
// stack ISA v1. Runs every program.bin in the input dir on its input.bin and
// writes stdout.bin + exit.txt per instance. Semantics follow the kit's
// reference VM (program/generator/subject/vm.mjs), which is the rule where
// ISA.md could be read two ways.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table: per byte, imm | pops<<3 | pushes<<6; 255 = unknown opcode.
// imm is 0,1,2,4; pops/pushes are 0..3, so no valid entry reaches 255.
const T = new Uint8Array(256).fill(255);
const set = (ops: number[], imm: number, pops: number, pushes: number) => {
  for (const o of ops) T[o] = imm | (pops << 3) | (pushes << 6);
};
set([0x00, 0x34], 0, 0, 0); // HALT, RET
set([0x30, 0x33], 2, 0, 0); // JMP, CALL
set([0x01], 1, 0, 1); // PUSH8
set([0x02], 4, 0, 1); // PUSH32
set([0x03, 0x41, 0x50, 0x51, 0x53], 0, 1, 0); // POP, STORE, PRINT, PUTC, EXIT
set([0x31, 0x32], 2, 1, 0); // JZ, JNZ
set([0x04], 0, 1, 2); // DUP
set([0x05], 0, 2, 2); // SWAP
set([0x06], 0, 2, 3); // OVER
set([0x07], 0, 3, 3); // ROT
set([0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22], 0, 2, 1); // binary ops
set([0x17, 0x1b, 0x40], 0, 1, 1); // NEG, NOT, LOAD
set([0x52], 0, 0, 1); // IN

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let st = 0;
  const end = (code: number) => ({ out: out.subarray(0, ol), code });
  for (;;) {
    if (st === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const t = T[op];
    if (t === 255) return end(5);
    const imm = t & 7;
    if (pc + imm >= n) return end(9);
    st++;
    const nx = pc + 1 + imm;
    const pops = (t >> 3) & 3;
    const pushes = (t >> 6) & 3;
    if (sp < pops) return end(2);
    if (sp - pops + pushes > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const x = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = x; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = D[sp - 1];
        const v = D[sp - 2];
        if (a < 0 || a >= 256) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return end(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
