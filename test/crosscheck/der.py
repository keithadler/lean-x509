"""A small DER codec with knobs for writing it wrong, shared by the cross-library harness.

A node is a list [tag, value] where value is bytes (primitive) or a list of nodes (constructed). An
optional third element overrides how the node's length is written.
"""


def parse(b, i=0):
    t = b[i]
    i += 1
    l = b[i]
    i += 1
    if l & 0x80:
        n = l & 0x7F
        l = int.from_bytes(b[i:i + n], "big")
        i += n
    body = b[i:i + l]
    node = [t, [] if t & 0x20 else bytes(body)]
    if t & 0x20:
        j = 0
        while j < len(body):
            child, j = parse(body, j)
            node[1].append(child)
    return node, i + l


def tree(der):
    return parse(der)[0]


def enc_len(n):
    if n < 128:
        return bytes([n])
    bs = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(bs)]) + bs


def encode(node):
    t, v = node[0], node[1]
    body = b"".join(encode(c) for c in v) if t & 0x20 else v
    length = node[2](len(body)) if len(node) > 2 else enc_len(len(body))
    return bytes([t]) + length + body


def at(node, *path):
    for p in path:
        node = node[1][p]
    return node


def oid(dotted):
    arcs = [int(a) for a in dotted.split(".")]
    out = [40 * arcs[0] + arcs[1]]
    body = b""
    for a in [out[0]] + arcs[2:]:
        groups = [a & 0x7F]
        a >>= 7
        while a:
            groups.append(0x80 | (a & 0x7F))
            a >>= 7
        body += bytes(reversed(groups))
    return [0x06, body]
