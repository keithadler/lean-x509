// Java (OpenJDK): CertificateFactory to parse, the PKIX CertPathValidator that JSSE's PKIXValidator uses,
// then the serverAuth EKU check and JSSE's HostnameChecker for TLS.
import java.io.ByteArrayInputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.cert.*;
import java.util.*;
import sun.security.util.HostnameChecker;

public class Main {
    public static void main(String[] args) throws Exception {
        Path dir = Path.of(args[0]);
        long now = Long.parseLong(Files.readString(dir.resolve("now.txt")).trim());
        CertificateFactory cf = CertificateFactory.getInstance("X.509");
        for (String line : Files.readAllLines(dir.resolve("manifest.tsv"))) {
            String[] f = line.split("\t", -1);
            String id = f[0];
            try {
                X509Certificate leaf = load(cf, dir.resolve(f[1]));
                List<X509Certificate> path = new ArrayList<>(List.of(leaf));
                for (String n : f[2].isEmpty() ? new String[0] : f[2].split(",")) path.add(load(cf, dir.resolve(n)));
                X509Certificate anchor = load(cf, dir.resolve(f[3]));
                PKIXParameters p = new PKIXParameters(Set.of(new TrustAnchor(anchor, null)));
                p.setRevocationEnabled(false);
                p.setDate(new Date(now * 1000));
                CertPathValidator.getInstance("PKIX").validate(cf.generateCertPath(path), p);
                List<String> eku = leaf.getExtendedKeyUsage();
                if (eku != null && !eku.contains("1.3.6.1.5.5.7.3.1") && !eku.contains("2.5.29.37.0"))
                    throw new CertificateException("extKeyUsage does not allow serverAuth");
                HostnameChecker.getInstance(HostnameChecker.TYPE_TLS).match(f[4], leaf);
                System.out.println("{\"id\":\"" + id + "\",\"ok\":true}");
            } catch (Exception e) {
                String msg = (e.getClass().getSimpleName() + ": " + e.getMessage()).replace("\\", "\\\\").replace("\"", "'");
                System.out.println("{\"id\":\"" + id + "\",\"ok\":false,\"err\":\"" + msg.replace("\n", " ") + "\"}");
            }
        }
    }

    static X509Certificate load(CertificateFactory cf, Path p) throws Exception {
        return (X509Certificate) cf.generateCertificate(new ByteArrayInputStream(Files.readAllBytes(p)));
    }
}
