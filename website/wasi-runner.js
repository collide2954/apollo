const encoder = new TextEncoder();
const decoder = new TextDecoder("utf-8");

class WasiExit extends Error {
  constructor(code) {
    super(`WASI proc_exit(${code})`);
    this.code = code;
  }
}

export function runApolloWasm(wasmModule, command, source) {
  const argStrings = ["apollo-wasm", command];
  const encodedArgs = argStrings.map((s) => encoder.encode(`${s}\0`));
  const totalArgBytes = encodedArgs.reduce((acc, b) => acc + b.length, 0);

  const stdinBytes = encoder.encode(source);
  let stdinOffset = 0;
  const stdoutChunks = [];
  const stderrChunks = [];
  let memory = null;

  const view = () => new DataView(memory.buffer);
  const bytes = () => new Uint8Array(memory.buffer);

  const imports = {
    wasi_snapshot_preview1: {
      args_sizes_get(argcPtr, argvBufSizePtr) {
        const dv = view();
        dv.setUint32(argcPtr, encodedArgs.length, true);
        dv.setUint32(argvBufSizePtr, totalArgBytes, true);
        return 0;
      },
      args_get(argvPtr, argvBufPtr) {
        const dv = view();
        const mem = bytes();
        let bufCursor = argvBufPtr;
        for (let i = 0; i < encodedArgs.length; i += 1) {
          dv.setUint32(argvPtr + i * 4, bufCursor, true);
          mem.set(encodedArgs[i], bufCursor);
          bufCursor += encodedArgs[i].length;
        }
        return 0;
      },
      environ_sizes_get(countPtr, bufSizePtr) {
        const dv = view();
        dv.setUint32(countPtr, 0, true);
        dv.setUint32(bufSizePtr, 0, true);
        return 0;
      },
      environ_get() {
        return 0;
      },
      clock_time_get(_id, _precision, timePtr) {
        const dv = view();
        const ns = BigInt(Date.now()) * 1000000n;
        dv.setBigUint64(timePtr, ns, true);
        return 0;
      },
      random_get(bufPtr, bufLen) {
        const target = bytes().subarray(bufPtr, bufPtr + bufLen);
        if (globalThis.crypto && typeof globalThis.crypto.getRandomValues === "function") {
          globalThis.crypto.getRandomValues(target);
        } else {
          for (let i = 0; i < target.length; i += 1) {
            target[i] = (i * 31 + 17) & 0xff;
          }
        }
        return 0;
      },
      fd_read(fd, iovsPtr, iovsLen, nreadPtr) {
        if (fd !== 0) {
          return 8;
        }
        const dv = view();
        const mem = bytes();
        let total = 0;
        for (let i = 0; i < iovsLen; i += 1) {
          const ptr = dv.getUint32(iovsPtr + i * 8, true);
          const len = dv.getUint32(iovsPtr + i * 8 + 4, true);
          const remaining = stdinBytes.length - stdinOffset;
          if (remaining <= 0) {
            break;
          }
          const toCopy = Math.min(len, remaining);
          mem.set(stdinBytes.subarray(stdinOffset, stdinOffset + toCopy), ptr);
          stdinOffset += toCopy;
          total += toCopy;
        }
        dv.setUint32(nreadPtr, total, true);
        return 0;
      },
      fd_write(fd, iovsPtr, iovsLen, nwrittenPtr) {
        if (fd !== 1 && fd !== 2) {
          return 8;
        }
        const dv = view();
        const mem = bytes();
        const sink = fd === 1 ? stdoutChunks : stderrChunks;
        let total = 0;
        for (let i = 0; i < iovsLen; i += 1) {
          const ptr = dv.getUint32(iovsPtr + i * 8, true);
          const len = dv.getUint32(iovsPtr + i * 8 + 4, true);
          sink.push(mem.slice(ptr, ptr + len));
          total += len;
        }
        dv.setUint32(nwrittenPtr, total, true);
        return 0;
      },
      proc_exit(code) {
        throw new WasiExit(code);
      },
    },
  };

  const instance = new WebAssembly.Instance(wasmModule, imports);
  memory = instance.exports.memory;

  let exitCode = 0;
  try {
    instance.exports._start();
  } catch (err) {
    if (err instanceof WasiExit) {
      exitCode = err.code;
    } else {
      throw err;
    }
  }

  const totalOut = stdoutChunks.reduce((acc, c) => acc + c.length, 0);
  const merged = new Uint8Array(totalOut);
  let pos = 0;
  for (const chunk of stdoutChunks) {
    merged.set(chunk, pos);
    pos += chunk.length;
  }
  const text = decoder.decode(merged);
  const result = JSON.parse(text);
  result.exit_code = exitCode;
  return result;
}
