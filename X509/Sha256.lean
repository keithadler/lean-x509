/-!
# SHA-256 (FIPS 180-4)

Written on natural numbers rather than `UInt32`, because Lean's kernel computes `Nat` arithmetic and bit
operations with GMP. That is what lets the kernel itself hash a real certificate: the checks below and the
chain in `X509.Chain` are proved by `decide +kernel`, with no compiled code involved.

A word is a `Nat` below 2³²; every operation reduces its result back into that range.
-/

namespace X509.Sha256

def M32 : Nat := 0xFFFFFFFF

def add (a b : Nat) : Nat := (a + b) &&& M32
def rotr (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (32 - n))) &&& M32
def notw (x : Nat) : Nat := M32 - (x &&& M32)

def ch (x y z : Nat) : Nat := (x &&& y) ^^^ (notw x &&& z)
def maj (x y z : Nat) : Nat := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bsig0 (x : Nat) : Nat := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bsig1 (x : Nat) : Nat := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def ssig0 (x : Nat) : Nat := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def ssig1 (x : Nat) : Nat := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The 64 round constants: the first 32 bits of the fractional parts of the cube roots of the first 64
primes. -/
def K : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value: the first 32 bits of the fractional parts of the square roots of the first 8
primes. -/
def H0 : List Nat :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Big-endian 32-bit words of a block of bytes. -/
def words : List Nat → List Nat
  | a :: b :: c :: d :: rest => (a <<< 24 ||| b <<< 16 ||| c <<< 8 ||| d) :: words rest
  | _ => []

/-- The message schedule: the block's 16 words, then 48 more, each from four earlier ones. -/
def schedule (w : List Nat) : List Nat :=
  let rec go : Nat → List Nat → List Nat → List Nat
    | 0, _, acc => acc.reverse
    | n + 1, win, acc =>
      match win with
      | w0 :: w1 :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: w9 :: _ :: _ :: _ :: _ :: w14 :: _ :: [] =>
        let x := add (add (ssig1 w14) w9) (add (ssig0 w1) w0)
        go n (win.tail ++ [x]) (x :: acc)
      | _ => acc.reverse
  w ++ go 48 w []

structure State where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat

def round (s : State) (k w : Nat) : State :=
  let t1 := add (add (add s.h (bsig1 s.e)) (add (ch s.e s.f s.g) k)) w
  let t2 := add (bsig0 s.a) (maj s.a s.b s.c)
  { a := add t1 t2, b := s.a, c := s.b, d := s.c, e := add s.d t1, f := s.e, g := s.f, h := s.g }

def compress (hv : List Nat) (block : List Nat) : List Nat :=
  match hv with
  | [a, b, c, d, e, f, g, h] =>
    let s := (K.zip (schedule (words block))).foldl (fun s (k, w) => round s k w) ⟨a, b, c, d, e, f, g, h⟩
    [add a s.a, add b s.b, add c s.c, add d s.d, add e s.e, add f s.f, add g s.g, add h s.h]
  | _ => hv

/-- The big-endian bytes of `n`, exactly `k` of them. -/
def bytesBE : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => bytesBE k (n >>> 8) ++ [n &&& 0xFF]

/-- Padding: a `0x80` byte, zeros up to 56 mod 64, then the length in bits as 8 bytes. -/
def pad (msg : List Nat) : List Nat :=
  let l := msg.length
  msg ++ [0x80] ++ List.replicate ((119 - l % 64) % 64) 0 ++ bytesBE 8 (8 * l)

/-- Splits into 64-byte blocks. `fuel` is the number of blocks. -/
def blocks : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | n + 1, bs => bs.take 64 :: blocks n (bs.drop 64)

/-- The digest as a 256-bit number, which is how the RSA check below compares it. -/
def hashNat (msg : List Nat) : Nat :=
  let p := pad msg
  let hv := (blocks (p.length / 64) p).foldl compress H0
  hv.foldl (fun acc w => acc <<< 32 ||| w) 0

/-- The digest as 32 bytes. -/
def hash (msg : List Nat) : List Nat := bytesBE 32 (hashNat msg)

/-! ## Known answers from FIPS 180-4 and NIST's examples, checked by the kernel -/

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List Nat := s.toList.map Char.toNat

theorem sha256_abc :
    hashNat (ascii "abc") = 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad := by
  decide +kernel

theorem sha256_empty :
    hashNat [] = 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 := by
  decide +kernel

/-- The two-block example: 448 bits of message, so the padding spills into a second block. -/
theorem sha256_two_blocks :
    hashNat (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
      0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1 := by
  decide +kernel

end X509.Sha256
