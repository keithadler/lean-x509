//! rustls-webpki (used by rustls): parse the leaf, verify the chain for server auth, then the host.
use rustls_pki_types::{CertificateDer, ServerName, UnixTime};
use std::{fs, path::Path, time::Duration};
use webpki::{EndEntityCert, KeyUsage};

fn main() {
    let dir = std::env::args().nth(1).expect("corpus dir");
    let dir = Path::new(&dir);
    let m: serde_json::Value = serde_json::from_slice(&fs::read(dir.join("manifest.json")).unwrap()).unwrap();
    let now = UnixTime::since_unix_epoch(Duration::from_secs(m["now"].as_u64().unwrap()));
    for c in m["cases"].as_array().unwrap() {
        let id = c["id"].as_str().unwrap();
        let read = |n: &serde_json::Value| CertificateDer::from(fs::read(dir.join(n.as_str().unwrap())).unwrap());
        let leaf_der = read(&c["leaf"]);
        let chain: Vec<CertificateDer> = c["chain"].as_array().unwrap().iter().map(read).collect();
        let anchor_der = read(&c["anchor"]);
        let result = (|| -> Result<(), String> {
            let anchor = webpki::anchor_from_trusted_cert(&anchor_der).map_err(|e| format!("anchor: {e:?}"))?;
            let ee = EndEntityCert::try_from(&leaf_der).map_err(|e| format!("parse: {e:?}"))?;
            ee.verify_for_usage(webpki::ALL_VERIFICATION_ALGS, &[anchor], &chain, now,
                KeyUsage::server_auth(), None, None).map_err(|e| format!("verify: {e:?}"))?;
            let host = ServerName::try_from(c["host"].as_str().unwrap()).map_err(|e| format!("host: {e:?}"))?;
            ee.verify_is_valid_for_subject_name(&host).map_err(|e| format!("name: {e:?}"))?;
            Ok(())
        })();
        let out = match result {
            Ok(()) => serde_json::json!({"id": id, "ok": true}),
            Err(e) => serde_json::json!({"id": id, "ok": false, "err": e}),
        };
        println!("{out}");
    }
}
