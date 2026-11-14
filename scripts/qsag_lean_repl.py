#!/usr/bin/env python3
"""qsag-lean-repl: Zero-trust sub-250ms incremental Lean 4.35 daemon for bb2/hbox."""
import argparse, json, os, resource, socket, subprocess, sys, time

DEFAULT_LEAN = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")

def u16_len(s: str) -> int:
    return len(s.encode("utf-16-le")) // 2

class QsagLeanSession:
    def __init__(self, repo_lean_dir: str, lean_bin: str = DEFAULT_LEAN, rss_gb: int = 12):
        self.repo = os.path.abspath(repo_lean_dir)
        env = os.environ.copy()
        bdir = os.path.join(self.repo, ".lake", "build", "lib", "lean")
        env["LEAN_PATH"] = bdir + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        limit_bytes = rss_gb * 1024 * 1024 * 1024
        def _preexec():
            resource.setrlimit(resource.RLIMIT_AS, (limit_bytes, limit_bytes))
        self.proc = subprocess.Popen(
            [lean_bin, "-Dexperimental.module=true", "-DautoImplicit=false", "--server"],
            cwd=self.repo, env=env, preexec_fn=_preexec,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        )
        self.seq = 0
        self.diags, self.progress, self.mounts = {}, {}, {}
        self._req("initialize", {"processId": os.getpid(), "rootUri": f"file://{self.repo}", "capabilities": {}})
        self._send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

    def _send(self, msg: dict) -> None:
        body = json.dumps(msg).encode("utf-8")
        self.proc.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body)
        self.proc.stdin.flush()

    def _recv(self) -> dict:
        headers = {}
        while True:
            line = self.proc.stdout.readline().decode("ascii")
            if not line:
                raise EOFError("lean --server closed stdout")
            if line == "\r\n":
                break
            if ":" in line:
                k, v = line.split(":", 1)
                headers[k.strip().lower()] = v.strip()
        return json.loads(self.proc.stdout.read(int(headers["content-length"])).decode("utf-8"))

    def _handle(self, m: dict) -> None:
        method = m.get("method")
        if method == "textDocument/publishDiagnostics":
            p = m["params"]
            self.diags[(p["uri"], p.get("version"))] = p["diagnostics"]
        elif method == "$/lean/fileProgress":
            p = m["params"]
            self.progress[(p["textDocument"]["uri"], p["textDocument"].get("version"))] = p["processing"]
        elif method is not None and "id" in m:
            self._send({"jsonrpc": "2.0", "id": m["id"], "result": None})

    def _req(self, method: str, params: dict):
        self.seq += 1
        rid = self.seq
        self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        while True:
            m = self._recv()
            if m.get("id") == rid and "method" not in m:
                return m.get("result")
            self._handle(m)

    def _sync(self, uri: str, ver: int) -> None:
        while self.progress.get((uri, ver)) != []:
            self._handle(self._recv())
        self._req("textDocument/waitForDiagnostics", {"uri": uri, "version": ver})

    def mount(self, key: str, mode: str, target: str, line_limit: int = 0, ns: str = "Qsag") -> dict:
        t0 = time.perf_counter()
        uri = f"file://{self.repo}/Qsag/_Repl_{key}.lean"
        if mode == "import_all":  # Tier-A: ~740 ms cold, ~203 ms/probe!
            base = [
                "module", f"public import {target}", f"import all {target}",
                "public import Qsag.Tactic.AssuranceKit", "public section", f"namespace {ns}",
            ]
            closer = f"end {ns}\nend\n"
        else:  # Tier-B: raw file prefix up to line_limit
            raw = open(os.path.join(self.repo, target), encoding="utf-8").read().split("\n")
            base = raw[:line_limit] if line_limit > 0 else raw
            closer = "\n"
        tail = base[-1] + "\n" + closer
        ver = 1
        self._send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {"uri": uri, "languageId": "lean4", "version": ver, "text": "\n".join(base[:-1] + [tail])}
        }})
        self._sync(uri, ver)
        self.mounts[key] = {"uri": uri, "ver": ver, "base_last": base[-1], "anchor": len(base) - 1,
                            "prev_tail": tail, "closer": closer}
        return {"ok": True, "ms": round((time.perf_counter() - t0) * 1000, 1),
                "init_diags": self.diags.get((uri, ver), [])}

    def eval_snippet(self, key: str, snippet: str, goal_lines: list[int] = (), verify_decl: str = "") -> dict:
        st = self.mounts[key]
        st["ver"] += 1
        ver, uri, el = st["ver"], st["uri"], st["anchor"]
        body = snippet + (f"\n#verify_constructive {verify_decl}" if verify_decl else "")
        new_tail = st["base_last"] + "\n" + body + "\n" + st["closer"]
        old_lines = st["prev_tail"].split("\n")
        t0 = time.perf_counter()
        self._send({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
            "textDocument": {"uri": uri, "version": ver},
            "contentChanges": [{"range": {"start": {"line": el, "character": 0},
                                          "end": {"line": el + len(old_lines) - 1, "character": u16_len(old_lines[-1])}},
                                "text": new_tail}],
        }})
        st["prev_tail"] = new_tail
        self._sync(uri, ver)
        snip_lines = body.split("\n")
        goals = {}
        for off in goal_lines:
            if 0 <= off < len(snip_lines):
                res = self._req("$/lean/plainGoal", {
                    "textDocument": {"uri": uri},
                    "position": {"line": el + 1 + off, "character": u16_len(snip_lines[off])},
                })
                goals[off] = res.get("goals", []) if res else []
        ds = [{"line": d["range"]["start"]["line"] - el, "severity": d.get("severity"), "message": d["message"]}
              for d in self.diags.get((uri, ver), []) if d["range"]["start"]["line"] >= el]
        return {"ok": not any(d["severity"] == 1 for d in ds),
                "ms": round((time.perf_counter() - t0) * 1000, 1), "diagnostics": ds, "goals": goals}

def serve(sock_path: str, repo: str) -> None:
    if os.path.exists(sock_path):
        os.unlink(sock_path)
    sess = QsagLeanSession(repo)
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    srv.bind(sock_path)
    srv.listen(8)
    while True:
        conn, _ = srv.accept()
        with conn:
            req = json.loads(conn.makefile("r", encoding="utf-8").readline())
            cmd = req["cmd"]
            out = sess.mount(**req["args"]) if cmd == "mount" else sess.eval_snippet(**req["args"])
            conn.sendall((json.dumps(out) + "\n").encode("utf-8"))

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--sock", default=f"/tmp/qsag-lean-repl-{os.getuid()}.sock")
    ap.add_argument("action", choices=["serve", "mount", "eval"])
    ap.add_argument("--repo", default="/home/build/qsag-conv/lean")
    ap.add_argument("--payload", default="{}")
    a = ap.parse_args()
    if a.action == "serve":
        serve(a.sock, a.repo)
    else:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
            s.connect(a.sock)
            s.sendall((json.dumps({"cmd": a.action, "args": json.loads(a.payload)}) + "\n").encode("utf-8"))
            print(s.makefile("r", encoding="utf-8").readline(), end="")
