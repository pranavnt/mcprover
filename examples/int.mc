// filename: int.mc

use mc:Type;
use mc:Eq;
use mc:Forall;
use mc:Exists;
use mc:Induction;

type Int: Type;

enum Int {
    Zero,
    Dec(Int),
    Inc(Int),
}

type dec = Int -> Int;
type inc = Int -> Int;

impl dec for Int {
    cases self {
        Int::Zero => Int::Dec(Int::Zero),
        Int::Dec(x) => Int::Dec(Int::Dec(x)),
        Int::Inc(x) => x,
    }
}

impl inc for Int {
    cases self {
        Int::Zero => Int::Inc(Int::Zero),
        Int::Dec(x) => x,
        Int::Inc(x) => Int::Inc(Int::Inc(x)),
    }
}

type add = (Int, Int) -> Int;
type sub = (Int, Int) -> Int;
type mul = (Int, Int) -> Int;

impl add for Int {
    cases self {
        Int::Zero => other,
        Int::Dec(x) => x.add(other).dec(),
        Int::Inc(x) => x.add(other).inc(),
    }
}

impl sub for Int {
    fn sub(self, other: Int) -> Int {
        match other {
            Int::Zero => self,
            Int::Dec(y) => self.add(y.inc()),
            Int::Inc(y) => self.add(y.dec()),
        }
    }
}

impl mul for Int {
    fn mul(self, other: Int) -> Int {
        match self {
            Int::Zero => Int::Zero,
            Int::Dec(x) => other.add(x.mul(other).dec()),
            Int::Inc(x) => other.add(x.mul(other)),
        }
    }
}

theorem add_comm: Forall<Int, Int>(|x, y| x.add(y) == y.add(x));
theorem add_assoc: Forall<Int, Int, Int>(|x, y, z| x.add(y).add(z) == x.add(y.add(z)));
theorem mul_comm: Forall<Int, Int>(|x, y| x.mul(y) == y.mul(x));
theorem mul_assoc: Forall<Int, Int, Int>(|x, y, z| x.mul(y).mul(z) == x.mul(y.mul(z)));
theorem add_zero: Forall<Int>(|x| x.add(Int::Zero) == x);
theorem mul_one: Forall<Int>(|x| x.mul(Int::Inc(Int::Zero)) == x);


"(a + b) = c"
- c
--+
---a
---b