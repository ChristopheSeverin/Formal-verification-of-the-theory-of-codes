module

public import Mathlib.Data.Nat.Bitwise

/-! # The finite search behind Lemma 7: the checker

A candidate code has `s` letter codewords `[0], …, [s-1]` and long words of lengths `lens`
(nondecreasing, at least two). The letters of the long words are numbered by first appearance,
the letter codewords and the other letters separately, so the concatenation `q` of the long
words is a two-counter restricted growth string. The search runs over these strings, prunes
subtrees on which a reduction always applies, and at each leaf either applies a quick reduction
or checks a certificate: a prefix tree for Lemma 6, or two different parsings of one word.

Words are handled through their base `8` codes (most significant letter first), so every test
is a small number of arithmetic operations, which the kernel evaluates with big numbers. The
soundness of the checker is proved in `SearchSound`. -/

@[expose] public section

namespace SmallestNoncompletable.Search

/-! ## Arithmetic helpers -/

/-- Bit `x` of `m`. -/
def bit (m x : ℕ) : ℕ := Nat.land (Nat.shiftRight m x) 1

/-- `8 ^ n`. -/
def p8 (n : ℕ) : ℕ := Nat.shiftLeft 1 (3 * n)

def maxN (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

def minN (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

/-- Membership in a list of numbers. -/
def memN (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => Nat.beq x y || memN x ys

/-- Number of `x` with `s ≤ x < s + n` whose bit is clear in `m`. -/
def missing (m s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => missing m s n + (1 - bit m (s + n))

/-! ## Profiles -/

/-- A profile: the number `s` of letter codewords and the lengths of the long words. -/
structure Prof where
  s : ℕ
  lens : List ℕ

/-- Total length of the long words. -/
def Prof.m (P : Prof) : ℕ := P.lens.sum

/-- Number of long words. -/
def Prof.t (P : Prof) : ℕ := P.lens.length

/-- Position `i` is the first position of a long word. -/
def isStart : List ℕ → ℕ → Bool
  | [], _ => false
  | l :: ls, i => Nat.beq i 0 || (Nat.ble l i && isStart ls (i - l))

/-- Position `i` is the last position of a long word. -/
def isEnd : List ℕ → ℕ → Bool
  | [], _ => false
  | l :: ls, i => Nat.beq (i + 1) l || (Nat.ble l i && isEnd ls (i - l))

/-- Number of long words starting at a position `≥ i`. -/
def remStarts : List ℕ → ℕ → ℕ
  | [], _ => 0
  | l :: ls, i => cond (Nat.beq i 0) 1 0 + remStarts ls (i - l)

/-- Number of long words ending at a position `≥ i`. -/
def remEnds : List ℕ → ℕ → ℕ
  | [], _ => 0
  | l :: ls, i => cond (Nat.blt i l) 1 0 + remEnds ls (i - l)

/-- If position `i` follows a long word which is not the last one, the number of long words
before position `i`, else `0`. -/
def doneCount : List ℕ → ℕ → ℕ
  | [], _ => 0
  | [_], _ => 0
  | _ :: _ :: _, 0 => 0
  | l :: l' :: ls, i + 1 => cond (Nat.beq (i + 1) l) 1
      (cond (Nat.blt l (i + 1)) (let n := doneCount (l' :: ls) (i + 1 - l); cond (Nat.beq n 0) 0 (n + 1)) 0)

/-! ## Codes of words -/

/-- The codes of the long words of a pattern with code `acc`, given the lengths and the total
length of the long words still to the right. -/
def wordCodes (acc : ℕ) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | l :: ls, r => (acc / p8 (r - l)) % p8 l :: wordCodes acc ls (r - l)

/-- The word list as pairs (code, length): letter codewords first. -/
def wordList (s : ℕ) (lens : List ℕ) (acc : ℕ) : List (ℕ × ℕ) :=
  (List.range s).map (fun x => (x, 1)) ++ (wordCodes acc lens lens.sum).zip lens

/-! ## Quick tests at a leaf -/

/-- Two long words are equal. -/
def dupB : List (ℕ × ℕ) → Bool
  | [] => false
  | w :: ws => ws.any (fun v => Nat.beq w.1 v.1 && Nat.beq w.2 v.2) || dupB ws

/-- `v` is a proper prefix of `w`. -/
def properPrefix (v w : ℕ × ℕ) : Bool := Nat.blt v.2 w.2 && Nat.beq (w.1 / p8 (w.2 - v.2)) v.1

/-- `v` is a proper suffix of `w`. -/
def properSuffix (v w : ℕ × ℕ) : Bool := Nat.blt v.2 w.2 && Nat.beq (w.1 % p8 v.2) v.1

/-- No long word starts with a letter codeword or is a proper prefix of another long word. -/
def prefixFreeB (s : ℕ) (longs : List (ℕ × ℕ)) : Bool :=
  longs.all (fun w => Nat.ble s (w.1 / p8 (w.2 - 1))) &&
    longs.all fun v => longs.all fun w => !properPrefix v w

def suffixFreeB (s : ℕ) (longs : List (ℕ × ℕ)) : Bool :=
  longs.all (fun w => Nat.ble s (w.1 % 8)) &&
    longs.all fun v => longs.all fun w => !properSuffix v w

/-! ## Certificates -/

/-- Base `16` digits, least significant first. -/
def digits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n => cond (Nat.beq n 0) [] (n % 16 :: digits fuel (n / 16))

/-- Read internal nodes, each given by its length and its letters, as codes with a leading
`1`. -/
def nodes : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | _, [] => []
  | fuel + 1, l :: ds => (ds.take l).foldl (fun c x => 8 * c + x) 1 :: nodes fuel (ds.drop l)

/-- Read a word, from its most significant letter, through the tree with internal nodes `I`
(codes with a leading `1`), starting from `node`; `n` letters remain. -/
def readF (I : List ℕ) (c : ℕ) : ℕ → ℕ → Bool
  | 0, node => Nat.beq node 1
  | n + 1, node =>
    let node' := 8 * node + (c / p8 n) % 8
    cond (memN node' I) (readF I c n node') (readF I c n 1)

/-- Read a word from its least significant letter, that is, read the reversed word. -/
def readR (I : List ℕ) : ℕ → ℕ → ℕ → Bool
  | _, 0, node => Nat.beq node 1
  | c, n + 1, node =>
    let node' := 8 * node + c % 8
    cond (memN node' I) (readR I (c / 8) n node') (readR I (c / 8) n 1)

/-- All letters of a node code (below its leading `1`) are below `k`. -/
def lettersBelow (k : ℕ) : ℕ → ℕ → Bool
  | 0, e => Nat.beq e 1
  | fuel + 1, e => Nat.beq e 1 || (Nat.blt (e % 8) k && Nat.ble 8 e && lettersBelow k fuel (e / 8))

/-- Check a tree certificate. -/
def checkTree (ws : List (ℕ × ℕ)) (k : ℕ) (rev : Bool) (I : List ℕ) : Bool :=
  memN 1 I && I.all (fun e => Nat.beq e 1 || memN (e / 8) I) && I.all (lettersBelow k 8) &&
    ws.all (fun w => cond rev (readR I w.1 w.2 1) (readF I w.1 w.2 1)) && (List.range k).any fun x => memN (8 + x) I

/-- The code and length of the concatenation of the words with the given indices. -/
def concatCode (ws : List (ℕ × ℕ)) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | i :: is =>
    let w := ws.getD i (0, 0)
    let c := concatCode ws is
    (w.1 * p8 c.2 + c.1, w.2 + c.2)

/-- Check an ambiguity certificate: two lists of word indices with different first indices
and equal concatenations. -/
def checkAmb (ws : List (ℕ × ℕ)) : List ℕ → List ℕ → Bool
  | i :: l, j :: r => !Nat.beq i j && (i :: l).all (Nat.blt · ws.length) &&
      (j :: r).all (Nat.blt · ws.length) &&
      (let a := concatCode ws (i :: l); let b := concatCode ws (j :: r)
       Nat.beq a.1 b.1 && Nat.beq a.2 b.2)
  | _, _ => false

/-- A certificate is a number whose base `16` digits, the last one being a sentinel, are a tag
(`0`: tree, `1`: tree of the reversed code, `2`: ambiguity), then for a tree the internal nodes
as length-prefixed words, and for an ambiguity the length of the first index list followed by
the two lists. -/
def checkCert (ws : List (ℕ × ℕ)) (k c : ℕ) : Bool :=
  match (digits 64 c).dropLast with
  | 0 :: ds => checkTree ws k false (nodes 64 ds)
  | 1 :: ds => checkTree ws k true (nodes 64 ds)
  | 2 :: n :: ds => checkAmb ws (ds.take n) (ds.drop n)
  | _ => false

/-! ## The search -/

/-- The leaf test. -/
def leaf (P : Prof) (k acc : ℕ) (certs : List ℕ) : Option (List ℕ) :=
  let longs := (wordCodes acc P.lens P.m).zip P.lens
  cond (dupB longs || prefixFreeB P.s longs || suffixFreeB P.s longs) (some certs)
    (match certs with
     | [] => none
     | c :: cs => cond (checkCert ((List.range P.s).map (fun x => (x, 1)) ++ longs) k c)
         (some cs) none)

/-- Prune: there are as many other letters as long words, an endpoint letter can no longer be
placed, or a letter codeword can no longer be used while another one exists. -/
def prune (P : Prof) (i u k S E : ℕ) : Bool :=
  Nat.ble P.t (k - P.s) || Nat.blt (remStarts P.lens i) (missing S P.s (k - P.s)) ||
    Nat.blt (remEnds P.lens i) (missing E P.s (k - P.s)) ||
    (Nat.ble 2 P.s && Nat.blt (P.m - i) (P.s - u))

/-- `w` (code and length) is a concatenation of words of `dict`. -/
def isProduct (dict : List (ℕ × ℕ)) (c : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | 0, _ + 1 => false
  | fuel + 1, l + 1 => dict.any fun d => Nat.ble 1 d.2 && Nat.ble d.2 (l + 1) &&
      Nat.beq ((c % p8 (l + 1)) / p8 (l + 1 - d.2)) d.1 && isProduct dict c fuel (l + 1 - d.2)

/-- The length of the long word completed at position `i` (if it is not the last one). -/
def doneLen (P : Prof) (i : ℕ) : ℕ := P.lens.getD (doneCount P.lens i - 1) 0

/-- The letter codewords and the long words before the word completed at position `i`, as pairs
(code, length), from the code `acc` of the prefix. -/
def earlierWords (P : Prof) (i acc : ℕ) : List (ℕ × ℕ) :=
  let pre := P.lens.take (doneCount P.lens i - 1)
  (List.range P.s).map (fun x => (x, 1)) ++ (wordCodes (acc / p8 (doneLen P i)) pre pre.sum).zip pre

/-- When a long word other than the last one is complete, it must not repeat an earlier word
and must not be a product of earlier words. -/
def wordOK (P : Prof) (i acc : ℕ) : Bool :=
  cond (Nat.beq (doneCount P.lens i) 0) true
    (!(earlierWords P i acc).any (fun d => Nat.beq d.1 (acc % p8 (doneLen P i)) &&
        Nat.beq d.2 (doneLen P i)) &&
      !isProduct (earlierWords P i acc) (acc % p8 (doneLen P i)) (doneLen P i) (doneLen P i))

/-- Thread the certificates through the choices `a, a+1, …, a+n-1`. -/
def foldOpt (f : ℕ → List ℕ → Option (List ℕ)) (a n : ℕ) : List ℕ → Option (List ℕ) :=
  Nat.rec (motive := fun _ => ℕ → List ℕ → Option (List ℕ)) (fun _ cs => some cs)
    (fun _ ih a cs => match f a cs with
      | some cs' => ih (a + 1) cs'
      | none => none) n a

/-- The search over the long part. `i` is the position, `u` the number of letter codewords
used, `k` is `s` plus the number of other letters, `S` and `E` are the masks of the letters
which start or end a long word, `acc` is the code of the prefix. -/
def dfs (P : Prof) (fuel : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Option (List ℕ) :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Option (List ℕ))
    (fun i u k S E acc certs => cond (prune P i u k S E || !wordOK P i acc) (some certs)
        (leaf P k acc certs))
    (fun _ ih i u k S E acc certs => cond (prune P i u k S E || !wordOK P i acc) (some certs) (
      let st := isStart P.lens i
      let en := isEnd P.lens i
      let go := fun j cs => ih (i + 1) (cond (Nat.blt j P.s) (maxN u (j + 1)) u)
            (cond (Nat.ble P.s j) (maxN k (j + 1)) k)
            (cond st (Nat.lor S (Nat.shiftLeft 1 j)) S)
            (cond en (Nat.lor E (Nat.shiftLeft 1 j)) E) (8 * acc + j) cs
      match foldOpt go 0 (minN (u + 1) P.s) certs with
      | some cs => foldOpt go P.s (k + 1 - P.s) cs
      | none => none))
    fuel

/-- Run the search for a profile and check that all certificates are used. -/
def run (P : Prof) (certs : List ℕ) : Bool :=
  match dfs P P.m 0 0 P.s 0 0 0 certs with
  | some [] => true
  | _ => false

end SmallestNoncompletable.Search
