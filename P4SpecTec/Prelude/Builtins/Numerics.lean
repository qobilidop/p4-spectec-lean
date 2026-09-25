/-!
Numeric builtins. Mirrors `p4spec/lib/interface/builtin/numerics.ml`,
function for function, on Lean's `Int`. `Bigint`'s bitwise operations
are two's-complement on unbounded integers; Lean's core has `Int.not`
only, so `and`, `or` and `xor` are defined here by sign cases. A width or
shift above upstream's `max_bit_width` (2048) is an error there and
`none` here.
-/

namespace P4SpecTec.Prelude.Builtins.Numerics

/-- Mirrors `max_bit_width`. -/
def max_bit_width : Int := 2048

/-- Two's-complement bitwise and on unbounded integers. -/
def land (x y : Int) : Int :=
  match x, y with
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a - (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b - (b &&& a))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

/-- Two's-complement bitwise or. -/
def lor (x y : Int) : Int := Int.not (land (Int.not x) (Int.not y))

/-- Two's-complement bitwise xor. -/
def lxor (x y : Int) : Int := land (lor x y) (Int.not (land x y))

/-- Mirrors `shl'`. -/
def shl' (v : Int) (o : Nat) : Int := v * (2 ^ o)

/-- `dec $shl(int, int) : int`. -/
def shl (base offset : Int) : Option Int :=
  if offset > max_bit_width then none else some (shl' base offset.toNat)

/-- Mirrors `shr'`: repeated truncating halving. -/
def shr' (v : Int) : Nat → Int
  | 0 => v
  | o + 1 => shr' (Int.tdiv v 2) o

/-- `dec $shr(int, int) : int`. -/
def shr (base offset : Int) : Option Int :=
  if offset > max_bit_width then none else some (shr' base offset.toNat)

/-- Mirrors `shr_arith'`. -/
def shr_arith' (v : Int) (o : Nat) (m : Int) : Int :=
  match o with
  | 0 => v
  | o + 1 => shr_arith' (Int.tdiv v 2 + m) o m

/-- `dec $shr_arith(int, int, int) : int`. -/
def shr_arith (base offset modulus : Int) : Option Int :=
  if offset > max_bit_width then none else some (shr_arith' base offset.toNat modulus)

/-- Mirrors `pow2'`. -/
def pow2' (w : Int) : Int := shl' 1 w.toNat

/-- `dec $pow2(nat) : int`. -/
def pow2 (w : Int) : Int := pow2' w

/-- Mirrors `bitstr_to_int'`: reinterpret a bit string of width `w` as a
signed integer. Written with the fuel `w` gives, since the OCaml recurses
on the same width until the value is in range. -/
def bitstr_to_int' (w : Int) (n : Int) : Int :=
  if w ≤ 0 then 0
  else
    let w' := pow2' w
    let half := Int.tdiv w' 2
    -- one step of normalisation suffices for any input within one period;
    -- iterate a bounded number of times for inputs further away
    go (n.natAbs.log2 + 2) n w' half
where
  /-- The recursion of the OCaml, bounded by fuel. -/
  go : Nat → Int → Int → Int → Int
    | 0, n, _, _ => n
    | k + 1, n, w', half =>
      if n ≥ half then go k (n - w') w' half
      else if n < -half then go k (n + w') w' half
      else n

/-- `dec $bitstr_to_int(int, int) : int`. -/
def bitstr_to_int (width bitstr : Int) : Option Int :=
  if width > max_bit_width then none else some (bitstr_to_int' width bitstr)

/-- Mirrors `int_to_bitstr'`: the value modulo `2^w`, non-negative. -/
def int_to_bitstr' (w : Int) (n : Int) : Int := Int.emod n (pow2' w)

/-- `dec $int_to_bitstr(int, int) : int`. -/
def int_to_bitstr (width n : Int) : Option Int :=
  if width > max_bit_width then none else some (int_to_bitstr' width n)

/-- Mirrors `bits_to_int_unsigned'`: most significant bit first. -/
def bits_to_int_unsigned' (bits : List Bool) : Int :=
  bits.foldl (fun i b => i * 2 + if b then 1 else 0) 0

/-- `dec $bits_to_int_unsigned(bool*) : int`. -/
def bits_to_int_unsigned (bits : List Bool) : Int := bits_to_int_unsigned' bits

/-- Mirrors `bits_to_int_signed'`; `none` on the empty array, where upstream errors. -/
def bits_to_int_signed (bits : List Bool) : Option Int :=
  match bits with
  | [] => none
  | sign :: _ =>
    let u := bits_to_int_unsigned' bits
    some (if sign then u - 2 * (2 ^ (bits.length - 1) : Nat) else u)

/-- Mirrors `int_to_bits_unsigned'`: the low `width` bits, most significant first. -/
def int_to_bits_unsigned' (value : Int) (width : Nat) : List Bool :=
  ((List.range width).map fun i => decide (land value (shl' 1 i) > 0)).reverse

/-- `dec $int_to_bits_unsigned(nat, int) : bool*`. -/
def int_to_bits_unsigned (width value : Int) : Option (List Bool) :=
  if width > max_bit_width then none else some (int_to_bits_unsigned' value width.toNat)

/-- `dec $int_to_bits_signed(nat, int) : bool*`: the low bits of the
two's-complement representation. -/
def int_to_bits_signed (width value : Int) : Option (List Bool) :=
  if width > max_bit_width then none
  else
    let w := width.toNat
    let mask := shl' 1 w - 1
    some (int_to_bits_unsigned' (land value mask) w)

/-- `dec $bneg(int) : int`. -/
def bneg (i : Int) : Int := Int.not i

/-- `dec $band(int, int) : int`. -/
def band (l r : Int) : Int := land l r

/-- `dec $bxor(int, int) : int`. -/
def bxor (l r : Int) : Int := lxor l r

/-- `dec $bor(int, int) : int`. -/
def bor (l r : Int) : Int := lor l r

/-- Mirrors `bitacc'`: bits `l` to `m` of `n`; `none` for a negative `l`. -/
def bitacc (n m l : Int) : Option Int :=
  if l < 0 then none
  else
    let shifted := n >>> l.toNat
    let mask := pow2' (m + 1 - l) - 1
    some (land shifted mask)

/-- Mirrors `bitacc_replace'`. -/
def bitacc_replace (b m l r : Int) : Int :=
  let r := shl' r l.toNat
  let mask_hi := pow2' (m + 1) - 1
  let mask_lo := pow2' l - 1
  let mask := Int.not (lxor mask_hi mask_lo)
  lxor (land b mask) r

end P4SpecTec.Prelude.Builtins.Numerics
