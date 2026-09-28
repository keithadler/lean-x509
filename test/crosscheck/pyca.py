#!/usr/bin/env python3
"""Python `cryptography` (its Rust X.509 parser and path validator): parse, then verify as a server."""
import datetime as dt
import json
import os
import sys

from cryptography import x509
from cryptography.x509.verification import PolicyBuilder, Store

d = sys.argv[1]
m = json.load(open(os.path.join(d, "manifest.json")))
now = dt.datetime.fromtimestamp(m["now"], dt.timezone.utc)


def load(n):
    return x509.load_der_x509_certificate(open(os.path.join(d, n), "rb").read())


for c in m["cases"]:
    try:
        leaf = load(c["leaf"])
        chain = [load(n) for n in c["chain"]]
        store = Store([load(c["anchor"])])
        v = PolicyBuilder().store(store).time(now).build_server_verifier(x509.DNSName(c["host"]))
        v.verify(leaf, chain)
        print(json.dumps({"id": c["id"], "ok": True}))
    except Exception as e:  # noqa: BLE001
        print(json.dumps({"id": c["id"], "ok": False, "err": f"{type(e).__name__}: {e}"}))
