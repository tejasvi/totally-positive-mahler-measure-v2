# How the logs were produced

All runs of the two checkers used Linux x86-64 servers with 96 threads, Python 3.13.5 and python-flint 0.9.0 (FLINT
3.6.0), on 2026-10-21 (UTC), from a copy of this repository. The certificate had SHA-256
9f1e51157fbe30ce8ab436c8552d7d6a9b5aaaa5483449de00ec68716eac3864, and the checkers had the SHA-256 listed in
`SHA256SUMS`. The last line of every log, `exit status: N`, was appended by the shell.

- `logs/check_independent.log`: `python3 -I checker/check_independent.py certificate/tp_certificate.json 32`, then
- `logs/check_certificate.log`: `python3 -I checker/check_certificate.py certificate/tp_certificate.json 64`, one after
  the other on the same otherwise idle server.
- `logs/check_aux.log`: `python3 -I checker/check_aux.py certificate/tp_certificate.json`, run later on another Linux
  x86-64 server with Python 3.12.13 and the same python-flint 0.9.0 (FLINT 3.6.0).
- `tests/logs/first/<set>_<name>.log`: `python3 -I checker/check_certificate.py tests/work/<set>/<name>.json 32`.
- `tests/logs/second/<set>_<name>.log`: `python3 -I checker/check_independent.py tests/work/<set>/<name>.json 16`.

The modified certificates were written by `tests/run_all.sh python3 generate`. The test runs were spread over two servers
of the same type, with up to four checks running at a time, so their run times are not comparable with those of the
two runs on the certificate. Tracebacks in some test logs show the working directory of these runs.

In `logs/check_independent.log`, the text `(width <= 2^-99)` is a fixed label printed by the program. For this
certificate all 198 root windows have width exactly 2^-100.
