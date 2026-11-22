// Tiny stack VM: table-driven interpreter for make.fun's tiny stack ISA.
// One run answers every instance in the input directory. Node 22.
import { readdirSync, readFileSync, mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const STACK_CAP = 256;
const CALL_CAP = 64;
const MEM_WORDS = 256;
const STEP_CAP = 1000000;
const OUT_CAP = 65536;

// Traps: 2 underflow, 3 overflow, 4 div0, 5 opcode, 6 memory, 7 calls, 8 ret, 9 pc, 10 steps, 11 output.

type Core = {
  prog: Uint8Array;
  src: Uint8Array;
  out: Uint8Array;
  n: number;
  s: Int32Array;
  sp: number;
  c: Int32Array;
  cp: number;
  m: Int32Array;
  pc: number;
  steps: number;
  ip: number;
  end: boolean;
  code: number;
};

type Act = (v: Core, k: number) => void;
type Op = { imm: number; pops: number; pushes: number; act: Act };

const TABLE: (Op | null)[] = new Array(256).fill(null);

function reg(byte: number, imm: number, pops: number, pushes: number, act: Act): void {
  TABLE[byte] = { imm, pops, pushes, act };
}

function halt(v: Core, code: number): void {
  v.end = true;
  v.code = code;
}

function bin(f: (a: number, b: number) => number): Act {
  return (v) => {
    const b = v.s[v.sp - 1];
    const a = v.s[v.sp - 2];
    v.sp -= 2;
    v.s[v.sp++] = f(a, b) | 0;
  };
}

function rel(k: number): number {
  return (k << 16) >> 16;
}

// --- control ---
reg(0x00, 0, 0, 0, (v) => halt(v, 0));
reg(0x30, 2, 0, 0, (v, k) => { v.pc += rel(k); });
reg(0x31, 2, 1, 0, (v, k) => { if (v.s[--v.sp] === 0) v.pc += rel(k); });
reg(0x32, 2, 1, 0, (v, k) => { if (v.s[--v.sp] !== 0) v.pc += rel(k); });
reg(0x33, 2, 0, 0, (v, k) => {
  if (v.cp === CALL_CAP) return halt(v, 7);
  v.c[v.cp++] = v.pc;
  v.pc = k;
});
reg(0x34, 0, 0, 0, (v) => {
  if (v.cp === 0) return halt(v, 8);
  v.pc = v.c[--v.cp];
});

// --- stack ---
reg(0x01, 1, 0, 1, (v, k) => { v.s[v.sp++] = (k << 24) >> 24; });
reg(0x02, 4, 0, 1, (v, k) => { v.s[v.sp++] = k; });
reg(0x03, 0, 1, 0, (v) => { v.sp--; });
reg(0x04, 0, 1, 2, (v) => { v.s[v.sp] = v.s[v.sp - 1]; v.sp++; });
reg(0x05, 0, 2, 2, (v) => {
  const t = v.s[v.sp - 1];
  v.s[v.sp - 1] = v.s[v.sp - 2];
  v.s[v.sp - 2] = t;
});
reg(0x06, 0, 2, 3, (v) => { v.s[v.sp] = v.s[v.sp - 2]; v.sp++; });
reg(0x07, 0, 3, 3, (v) => {
  const a = v.s[v.sp - 3];
  v.s[v.sp - 3] = v.s[v.sp - 2];
  v.s[v.sp - 2] = v.s[v.sp - 1];
  v.s[v.sp - 1] = a;
});

// --- arithmetic ---
reg(0x10, 0, 2, 1, bin((a, b) => a + b));
reg(0x11, 0, 2, 1, bin((a, b) => a - b));
reg(0x12, 0, 2, 1, bin((a, b) => Math.imul(a, b)));
reg(0x13, 0, 2, 1, (v) => {
  const b = v.s[v.sp - 1];
  const a = v.s[v.sp - 2];
  if (b === 0) return halt(v, 4);
  v.sp -= 2;
  v.s[v.sp++] = a === -2147483648 && b === -1 ? a : (a / b) | 0;
});
reg(0x14, 0, 2, 1, (v) => {
  const b = v.s[v.sp - 1];
  const a = v.s[v.sp - 2];
  if (b === 0) return halt(v, 4);
  v.sp -= 2;
  v.s[v.sp++] = b === -1 ? 0 : (a % b) | 0;
});
reg(0x15, 0, 2, 1, (v) => {
  const b = v.s[v.sp - 1];
  const a = v.s[v.sp - 2];
  if (b === 0) return halt(v, 4);
  v.sp -= 2;
  v.s[v.sp++] = Math.floor((a >>> 0) / (b >>> 0)) | 0;
});
reg(0x16, 0, 2, 1, (v) => {
  const b = v.s[v.sp - 1];
  const a = v.s[v.sp - 2];
  if (b === 0) return halt(v, 4);
  v.sp -= 2;
  v.s[v.sp++] = ((a >>> 0) % (b >>> 0)) | 0;
});
reg(0x17, 0, 1, 1, (v) => { v.s[v.sp - 1] = -v.s[v.sp - 1] | 0; });
reg(0x18, 0, 2, 1, bin((a, b) => a & b));
reg(0x19, 0, 2, 1, bin((a, b) => a | b));
reg(0x1a, 0, 2, 1, bin((a, b) => a ^ b));
reg(0x1b, 0, 1, 1, (v) => { v.s[v.sp - 1] = ~v.s[v.sp - 1]; });
reg(0x1c, 0, 2, 1, bin((a, b) => a << (b & 31)));
reg(0x1d, 0, 2, 1, bin((a, b) => a >> (b & 31)));
reg(0x1e, 0, 2, 1, bin((a, b) => a >>> (b & 31)));
reg(0x20, 0, 2, 1, bin((a, b) => (a === b ? 1 : 0)));
reg(0x21, 0, 2, 1, bin((a, b) => (a < b ? 1 : 0)));
reg(0x22, 0, 2, 1, bin((a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0)));

// --- memory ---
reg(0x40, 0, 1, 1, (v) => {
  const a = v.s[v.sp - 1];
  if (a < 0 || a >= MEM_WORDS) return halt(v, 6);
  v.s[v.sp - 1] = v.m[a];
});
reg(0x41, 0, 2, 0, (v) => {
  const a = v.s[v.sp - 1];
  if (a < 0 || a >= MEM_WORDS) return halt(v, 6);
  v.m[a] = v.s[v.sp - 2];
  v.sp -= 2;
});

// --- input / output ---
// PRINT: decimal digits via a scratch buffer, no allocation.
// Uses the unsigned magnitude, so INT_MIN (-2147483648) prints correctly.
const DIG = new Uint8Array(12);

function printInt(v: Core, x: number): void {
  let mag = x < 0 ? -x : x;
  let d = 0;
  if (mag === 0) DIG[d++] = 48;
  else while (mag > 0) { DIG[d++] = 48 + (mag % 10); mag = Math.floor(mag / 10); }
  const len = d + (x < 0 ? 1 : 0);
  if (v.n + len > OUT_CAP) return halt(v, 11);
  v.sp--;
  if (x < 0) v.out[v.n++] = 45;
  while (d > 0) v.out[v.n++] = DIG[--d];
}

reg(0x50, 0, 1, 0, (v) => printInt(v, v.s[v.sp - 1]));
reg(0x51, 0, 1, 0, (v) => {
  if (v.n + 1 > OUT_CAP) return halt(v, 11);
  v.out[v.n++] = v.s[--v.sp] & 255;
});
reg(0x52, 0, 0, 1, (v) => {
  v.s[v.sp++] = v.ip < v.src.length ? v.src[v.ip++] : -1;
});
reg(0x53, 0, 1, 0, (v) => halt(v, v.s[--v.sp] & 255));

// --- the step loop ---
function run(prog: Uint8Array, src: Uint8Array): { out: Uint8Array; code: number } {
  const v: Core = {
    prog,
    src,
    out: new Uint8Array(OUT_CAP),
    n: 0,
    s: new Int32Array(STACK_CAP),
    sp: 0,
    c: new Int32Array(CALL_CAP),
    cp: 0,
    m: new Int32Array(MEM_WORDS),
    pc: 0,
    steps: 0,
    ip: 0,
    end: false,
    code: 0,
  };
  for (;;) {
    if (v.steps === STEP_CAP) { v.code = 10; break; }
    if (v.pc < 0 || v.pc >= prog.length) { v.code = 9; break; }
    const op = TABLE[prog[v.pc]];
    if (op === null) { v.code = 5; break; }
    if (v.pc + op.imm >= prog.length) { v.code = 9; break; }
    v.steps++;
    const nxt = v.pc + 1 + op.imm;
    if (v.sp < op.pops) { v.code = 2; break; }
    if (v.sp - op.pops + op.pushes > STACK_CAP) { v.code = 3; break; }
    let k = 0;
    if (op.imm === 1) k = prog[v.pc + 1];
    else if (op.imm === 2) k = prog[v.pc + 1] | (prog[v.pc + 2] << 8);
    else if (op.imm === 4) {
      k = prog[v.pc + 1] | (prog[v.pc + 2] << 8) | (prog[v.pc + 3] << 16) | (prog[v.pc + 4] << 24);
    }
    v.pc = nxt;
    op.act(v, k);
    if (v.end) break;
  }
  return { out: v.out.slice(0, v.n), code: v.code };
}

// --- driver ---
const inDir = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";

const ids = readdirSync(inDir, { withFileTypes: true })
  .filter((e) => e.isDirectory())
  .map((e) => e.name)
  .sort();

for (const id of ids) {
  const base = join(inDir, id);
  const prog = readFileSync(join(base, "program.bin"));
  let src: Buffer;
  try {
    src = readFileSync(join(base, "input.bin"));
  } catch {
    src = Buffer.alloc(0);
  }
  const { out, code } = run(prog, src);
  const od = join(outDir, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, "stdout.bin"), out);
  writeFileSync(join(od, "exit.txt"), `${code}\n`);
}
