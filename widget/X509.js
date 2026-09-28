import * as React from 'react';
const e = React.createElement;

// Every fact on this panel arrives from Lean (X509.Widget.widgetProps): the parsed DER trees, the decoded
// fields, the result of each chain check, and the tamper sweep. The JavaScript only lays them out.

const BG = '#0b0d12', PANEL = '#12151c', GRID = '#262c3a', INK = '#e8eaf0', DIM = '#8a90a2', FAINT = '#4a5163';
const GREEN = '#5fd4a0', RED = '#ff7a7a', AMBER = '#f2b35e', BLUE = '#7fb2ff', VIOLET = '#c29bff';
const MONO = "ui-monospace, 'SF Mono', Menlo, Consolas, monospace";
const SANS = "-apple-system, 'Segoe UI', Inter, Helvetica, Arial, sans-serif";

const hex2 = b => b.toString(16).padStart(2, '0');
const bytesOf = h => { const a = []; for (let i = 0; i < h.length; i += 2) a.push(parseInt(h.slice(i, i + 2), 16)); return a; };
const stamp = n => { const s = String(n); return `${s.slice(0, 4)}-${s.slice(4, 6)}-${s.slice(6, 8)} ${s.slice(8, 10)}:${s.slice(10, 12)}`; };
const days = n => { const s = String(n); return Date.UTC(+s.slice(0, 4), +s.slice(4, 6) - 1, +s.slice(6, 8)) / 864e5; };

// ---------- the DER tree, as Lean parsed it ----------

const TAGS = {
  0x01: 'BOOLEAN', 0x02: 'INTEGER', 0x03: 'BIT STRING', 0x04: 'OCTET STRING', 0x05: 'NULL', 0x06: 'OID',
  0x0c: 'UTF8String', 0x13: 'PrintableString', 0x16: 'IA5String', 0x17: 'UTCTime', 0x18: 'GeneralizedTime',
  0x30: 'SEQUENCE', 0x31: 'SET', 0xa0: '[0]', 0xa3: '[3]', 0x82: '[2] dNSName', 0x80: '[0]', 0x86: '[6] URI',
};
const OIDS = {
  '2.5.4.3': 'commonName', '2.5.4.6': 'countryName', '2.5.4.10': 'organizationName', '2.5.4.11': 'organizationalUnitName',
  '1.2.840.113549.1.1.1': 'rsaEncryption', '1.2.840.113549.1.1.11': 'sha256WithRSAEncryption',
  '2.5.29.19': 'basicConstraints', '2.5.29.15': 'keyUsage', '2.5.29.17': 'subjectAltName', '2.5.29.37': 'extKeyUsage',
  '2.5.29.14': 'subjectKeyIdentifier', '2.5.29.35': 'authorityKeyIdentifier', '2.5.29.32': 'certificatePolicies',
  '2.5.29.31': 'cRLDistributionPoints', '1.3.6.1.5.5.7.1.1': 'authorityInfoAccess', '1.3.6.1.5.5.7.3.1': 'serverAuth',
  '1.3.6.1.5.5.7.3.2': 'clientAuth', '1.3.6.1.4.1.11129.2.4.2': 'SCT list', '2.23.140.1.2.1': 'domain validated',
};
function oidText(bytes) {
  const arcs = []; let v = 0;
  bytes.forEach(b => { v = v * 128 + (b & 0x7f); if (b < 128) { arcs.push(v); v = 0; } });
  if (!arcs.length) return '';
  const f = arcs[0], first = f < 40 ? [0, f] : f < 80 ? [1, f - 40] : [2, f - 80];
  return first.concat(arcs.slice(1)).join('.');
}
const TBS = ['version', 'serialNumber', 'signature', 'issuer', 'validity', 'subject', 'subjectPublicKeyInfo', 'extensions'];

// Lays the tree out over the bytes: every node gets its offset, header length and content length.
function flatten(node, bytes, off = 0, depth = 0, path = [], out = []) {
  const item = { off, hdr: node.h, len: node.n, tag: node.t, depth, path, kids: node.c ? node.c.length : 0 };
  out.push(item);
  if (node.c) {
    let o = off + node.h;
    node.c.forEach((k, i) => { flatten(k, bytes, o, depth + 1, path.concat(i), out); o += k.h + k.n; });
  }
  return out;
}
function label(item, bytes, items) {
  const p = item.path, tag = TAGS[item.tag] || `tag ${hex2(item.tag)}`;
  let name = '';
  if (p.length === 0) name = 'Certificate';
  else if (p.length === 1) name = ['tbsCertificate', 'signatureAlgorithm', 'signatureValue'][p[0]];
  else if (p.length === 2 && p[0] === 0) {
    const hasVersion = items.some(x => x.path.length === 2 && x.path[0] === 0 && x.path[1] === 0 && x.tag === 0xa0);
    name = TBS[hasVersion ? p[1] : p[1] + 1] || '';
  }
  const content = bytes.slice(item.off + item.hdr, item.off + item.hdr + item.len);
  let value = '';
  if (item.tag === 0x06) { const o = oidText(content); value = OIDS[o] ? `${OIDS[o]} (${o})` : o; }
  else if ([0x0c, 0x13, 0x16, 0x17, 0x18, 0x82].includes(item.tag)) value = String.fromCharCode(...content);
  else if (item.tag === 0x01) value = content[0] === 0xff ? 'TRUE' : 'FALSE';
  else if (item.tag === 0x02 && item.len <= 4) value = String(content.reduce((a, b) => a * 256 + b, 0));
  else if (item.tag === 0x02) value = `${item.len} bytes`;
  else if (item.tag === 0x03) value = `${item.len - 1} bytes`;
  return { name, tag, value };
}

function DerView({ cert, hover, setHover }) {
  const bytes = React.useMemo(() => bytesOf(cert.der), [cert.der]);
  const items = React.useMemo(() => flatten(cert.tree, bytes), [cert.tree, bytes]);
  const sel = hover != null ? items[hover] : null;
  const role = i => !sel ? null : i >= sel.off && i < sel.off + 1 ? 'tag' : i < sel.off + sel.hdr && i >= sel.off ? 'len'
    : i >= sel.off + sel.hdr && i < sel.off + sel.hdr + sel.len ? 'body' : null;
  const colorOf = r => r === 'tag' ? VIOLET : r === 'len' ? AMBER : r === 'body' ? BLUE : null;
  const rows = [];
  const from = sel ? Math.max(0, Math.floor(sel.off / 16) - 1) * 16 : 0;
  for (let r = from; r < Math.min(bytes.length, from + 16 * 14); r += 16) rows.push(r);
  return e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: 14 } },
    e('div', { style: { flex: '1 1 330px', maxHeight: 360, overflowY: 'auto', fontFamily: MONO, fontSize: 11.5 } },
      items.map((it, i) => {
        const l = label(it, bytes, items);
        return e('div', {
          key: i, onMouseEnter: () => setHover(i),
          style: { paddingLeft: it.depth * 12, padding: '1px 4px 1px ' + (4 + it.depth * 12) + 'px', cursor: 'default',
            background: hover === i ? '#1d2433' : 'transparent', borderRadius: 3, whiteSpace: 'nowrap', overflow: 'hidden', textOverflow: 'ellipsis' },
        },
          l.name ? e('span', { style: { color: INK } }, l.name + ' ') : null,
          e('span', { style: { color: VIOLET } }, l.tag),
          e('span', { style: { color: FAINT } }, ` ${it.len}`),
          l.value ? e('span', { style: { color: GREEN } }, '  ' + l.value) : null);
      })),
    e('div', { style: { flex: '0 0 auto', fontFamily: MONO, fontSize: 11.5, lineHeight: '17px' } },
      rows.map(r => e('div', { key: r, style: { display: 'flex', gap: 6 } },
        e('span', { style: { color: FAINT, width: 34 } }, r.toString(16).padStart(4, '0')),
        e('span', null, bytes.slice(r, r + 16).map((b, j) => {
          const c = colorOf(role(r + j));
          return e('span', { key: j, style: { color: c || DIM, background: c ? c + '22' : 'transparent', padding: '0 1px', marginRight: 2 } }, hex2(b));
        })))),
      sel ? e('div', { style: { marginTop: 8, fontFamily: SANS, fontSize: 11.5, color: DIM, maxWidth: 420 } },
        e('span', { style: { color: VIOLET } }, 'tag '), e('span', { style: { color: AMBER } }, 'length '), e('span', { style: { color: BLUE } }, 'contents'),
        `  ·  offset ${sel.off}, ${sel.hdr} header byte${sel.hdr > 1 ? 's' : ''}, ${sel.len} content bytes. `,
        sel.len >= 128 ? `The length ${sel.len} needs the long form: 0x${hex2(0x80 + sel.hdr - 2)} then ${sel.hdr - 2} byte${sel.hdr > 3 ? 's' : ''}, the fewest possible, as der_unique requires.`
          : `The length ${sel.len} fits one byte, so DER writes one byte: a long form here would be refused.`)
        : e('div', { style: { marginTop: 8, fontFamily: SANS, fontSize: 11.5, color: DIM } }, 'Hover a node to see its bytes.')));
}

// ---------- the chain ----------

function Check({ ok, children, title }) {
  return e('span', { title, style: { display: 'inline-flex', alignItems: 'center', gap: 4, fontSize: 11, fontFamily: SANS,
    color: ok ? GREEN : RED, border: `1px solid ${ok ? GREEN + '55' : RED + '88'}`, borderRadius: 10, padding: '1px 7px' } },
    ok ? '✓' : '✗', children);
}

function Validity({ nb, na, now }) {
  const a = days(nb), b = days(na), n = days(now), lo = Math.min(a, n) - 20, hi = Math.max(b, n) + 20;
  const x = v => ((v - lo) / (hi - lo)) * 100;
  return e('div', { style: { position: 'relative', height: 14, margin: '6px 0 2px' } },
    e('div', { style: { position: 'absolute', left: x(a) + '%', width: (x(b) - x(a)) + '%', top: 5, height: 4, background: GREEN + '66', borderRadius: 2 } }),
    e('div', { style: { position: 'absolute', left: x(n) + '%', top: 0, width: 2, height: 14, background: INK } }));
}

function CertCard({ c, now, selected, onClick, matched, anchor }) {
  return e('div', {
    onClick, style: { background: selected ? '#18202e' : PANEL, border: `1px solid ${selected ? BLUE : GRID}`, borderRadius: 8,
      padding: '8px 10px', cursor: 'pointer' },
  },
    e('div', { style: { display: 'flex', justifyContent: 'space-between', gap: 8, alignItems: 'baseline' } },
      e('span', { style: { fontSize: 14, fontWeight: 600 } }, c.cn),
      e('span', { style: { fontSize: 11, color: DIM } }, anchor ? 'trust anchor' : c.isCA ? `CA${c.pathLen != null ? ` · pathLen ${c.pathLen}` : ''}` : 'leaf')),
    e('div', { style: { fontSize: 11, color: DIM, marginTop: 2 } }, `issued by ${c.issuerCn}  ·  RSA-${c.bits}`),
    e(Validity, { nb: c.notBefore, na: c.notAfter, now }),
    e('div', { style: { fontSize: 10.5, color: FAINT, fontFamily: MONO, display: 'flex', justifyContent: 'space-between' } },
      e('span', null, stamp(c.notBefore)), e('span', null, stamp(c.notAfter))),
    c.dns.length ? e('div', { style: { marginTop: 5, display: 'flex', flexWrap: 'wrap', gap: 4 } },
      c.dns.map(d => e('span', { key: d, style: { fontFamily: MONO, fontSize: 10.5, padding: '0 5px', borderRadius: 4,
        color: d === matched ? BG : DIM, background: d === matched ? GREEN : '#1a1f2a' } }, d))) : null);
}

function Link({ link }) {
  return e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: 5, padding: '6px 0 6px 18px', borderLeft: `2px solid ${GRID}`, marginLeft: 14 } },
    e(Check, { ok: link.names, title: 'child.issuer = parent.subject (names_chain)' }, 'names chain'),
    link.ca != null ? e(Check, { ok: link.ca, title: 'basicConstraints cA (issuers_are_CAs)' }, 'issuer is a CA') : null,
    link.ku != null ? e(Check, { ok: link.ku, title: 'keyUsage keyCertSign (issuers_may_sign)' }, 'may sign certificates') : null,
    e(Check, { ok: link.sig, title: 'Rsa.verify over the exact tbsCertificate bytes (signatures_verify, tbs_slice)' },
      `RSA-${link.bits} · SHA-256 signature`));
}

// ---------- the tamper sweep ----------

const OUTCOMES = [
  ['not DER', AMBER], ['decoder refuses', VIOLET], ['signature fails', RED], ['host or usage fails', BLUE], ['other check fails', DIM], ['VALID', '#ffffff'],
];

function Sweep({ sweep, der }) {
  const [at, setAt] = React.useState(null);
  const bytes = React.useMemo(() => bytesOf(der), [der]);
  const counts = OUTCOMES.map((_, k) => sweep.filter(x => x === k).length);
  const cols = 96;
  return e('div', null,
    e('div', { style: { fontSize: 12, color: DIM, marginBottom: 6, maxWidth: 760 } },
      `Change any one of the leaf's ${sweep.length} bytes (the lowest bit flipped) and validate the chain again, with the same compiled Lean code. Each cell is one byte: `,
      OUTCOMES.map(([n, c], k) => counts[k] ? e('span', { key: n, style: { color: c, marginRight: 10 } }, `■ ${n} ${counts[k]}`) : null),
      counts[5] === 0 ? e('span', { style: { color: GREEN } }, 'Not one survives.') : null),
    e('svg', { width: cols * 11, height: Math.ceil(sweep.length / cols) * 11, style: { display: 'block', width: '100%', height: 'auto' },
      viewBox: `0 0 ${cols * 11} ${Math.ceil(sweep.length / cols) * 11}` },
      sweep.map((k, i) => e('rect', { key: i, x: (i % cols) * 11, y: Math.floor(i / cols) * 11, width: 10, height: 10, rx: 1.5,
        fill: OUTCOMES[k][1], opacity: at === i ? 1 : 0.8, stroke: at === i ? '#fff' : 'none', onMouseEnter: () => setAt(i) }))),
    e('div', { style: { fontFamily: MONO, fontSize: 11.5, color: DIM, marginTop: 6, minHeight: 16 } },
      at == null ? 'Hover a cell.' : `byte ${at}: 0x${hex2(bytes[at])} → 0x${hex2(bytes[at] ^ 1)}   `,
      at == null ? null : e('span', { style: { color: OUTCOMES[sweep[at]][1] } }, OUTCOMES[sweep[at]][0])));
}

// ---------- theorems ----------

function Theorems({ list }) {
  return e('div', { style: { display: 'grid', gridTemplateColumns: 'repeat(auto-fill, minmax(290px, 1fr))', gap: 8 } },
    list.map(([name, what]) => e('div', { key: name, style: { background: PANEL, borderRadius: 6, padding: '6px 9px', border: `1px solid ${GRID}` } },
      e('div', { style: { fontFamily: MONO, fontSize: 11.5, color: GREEN } }, name),
      e('div', { style: { fontSize: 11.5, color: DIM, marginTop: 2 } }, what))));
}

const Section = (title, ...kids) => e('div', { style: { marginTop: 16 } },
  e('div', { style: { fontSize: 11, color: DIM, letterSpacing: 1.2, marginBottom: 8 } }, title), ...kids);

export default function X509Widget(props) {
  const [sel, setSel] = React.useState(0);
  const [hover, setHover] = React.useState(null);
  const certs = props.certs, n = certs.length;
  React.useEffect(() => setHover(null), [sel]);
  return e('div', { style: { background: BG, color: INK, borderRadius: 12, padding: 18, border: '1px solid #232838', fontFamily: SANS } },
    e('div', { style: { display: 'flex', justifyContent: 'space-between', flexWrap: 'wrap', gap: 8, borderBottom: `1px solid ${GRID}`, paddingBottom: 8 } },
      e('div', { style: { fontSize: 20, fontWeight: 700, letterSpacing: 1 } }, 'X.509, CHECKED BY LEAN'),
      e('div', { style: { fontSize: 12, color: DIM, alignSelf: 'flex-end' } }, 'core Lean · no Mathlib · decide +kernel')),
    e('div', { style: { display: 'flex', alignItems: 'center', gap: 12, flexWrap: 'wrap', margin: '14px 0 4px' } },
      e('span', { style: { fontFamily: MONO, fontSize: 16 } }, props.host),
      e('span', { style: { fontSize: 12, color: DIM } }, `at ${stamp(props.now)} UTC`),
      e('span', { style: { fontSize: 13, fontWeight: 700, color: props.valid ? BG : INK, background: props.valid ? GREEN : RED, borderRadius: 5, padding: '2px 10px' } },
        props.valid ? 'VALID' : 'INVALID'),
      e('span', { style: { fontSize: 11.5, color: DIM } }, 'theorem keithadler_github_io, by decide +kernel')),
    e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: 18, marginTop: 10 } },
      e('div', { style: { flex: '1 1 300px', maxWidth: 380 } },
        e('div', { style: { fontSize: 11, color: DIM, letterSpacing: 1.2, marginBottom: 8 } }, 'THE CHAIN  ·  CLICK A CERTIFICATE'),
        certs.map((c, i) => e(React.Fragment, { key: i },
          e(CertCard, { c, now: props.now, selected: sel === i, onClick: () => setSel(i), matched: i === 0 ? props.matched : null, anchor: i === n - 1 }),
          i < n - 1 ? e(Link, { link: props.links[i] }) : null))),
      e('div', { style: { flex: '2 1 460px', minWidth: 0 } },
        e('div', { style: { fontSize: 11, color: DIM, letterSpacing: 1.2, marginBottom: 8 } },
          `${certs[sel].cn.toUpperCase()}  ·  ${bytesOf(certs[sel].der).length} BYTES OF DER, AS LEAN PARSED THEM`),
        e('div', { style: { background: PANEL, borderRadius: 8, padding: 10 } }, e(DerView, { cert: certs[sel], hover, setHover })))),
    Section('TAMPER WITH IT', e('div', { style: { background: PANEL, borderRadius: 8, padding: 10 } }, e(Sweep, { sweep: props.sweep, der: certs[0].der }))),
    Section('WHAT IS PROVED', e(Theorems, { list: props.theorems })));
}
