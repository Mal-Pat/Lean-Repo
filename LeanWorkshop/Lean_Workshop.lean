import Mathlib




example (x : Nat) (h : x = 7) : x = 7 := h

example (x : Nat) : x = x := Eq.refl x

example (x : Nat) : 8 * (x ^ 2) - 5 = 8 * (x ^ 2) - 5 := Eq.refl _

example (x : Nat) (h : 7 = x) : x = 7 := Eq.symm h

example (x y : Nat) (h1 : x = 3) (h2 : y = x) : y = 3 := Eq.trans h2 h1

example (x y : Nat) (h1 : x = 3) (h2 : y = x) : y = 3 := Eq.subst h1 h2

--Starting to get cumbersome
example (x y : Nat) (h1 : x = 3) (h2 : x = y) : y = 3 := Eq.trans (Eq.symm h2) h1





theorem p_imp_p (x : Nat) (h : x = 0) : x = 0 := by
  exact h

#print p_imp_p

theorem same0r_2 (x : Nat) (h : x = 0) : 0 = x := by
  have h2 := Eq.comm.mp h
  exact h2

theorem same0r_1 (x : Nat) (h : x = 0) : 0 = x := by
  rw[h]

theorem same0l_1 (x : Nat) (h : 0 = x) : x = 0 := by
  rw[h]

#print same0l_1

#print same0r_1

theorem same0r_1' (x : Nat) (h : x = 0) : 0 = x :=
  (fun x h ↦
    let_fun h2 := Eq.comm.mp h;
    h2) x h

theorem same0r_1'' (x : Nat) : x = 0 → 0 = x :=
  (fun x h ↦
    let_fun h2 := Eq.comm.mp h;
    h2) x

theorem same0r_1''' : (x : Nat) → x = 0 → 0 = x :=
  fun x h ↦
    let_fun h2 := Eq.comm.mp h;
    h2

theorem same0r_1'''' : ∀ x : Nat, x = 0 → 0 = x :=
  fun x h ↦
    let_fun h2 := Eq.comm.mp h;
    h2

#check same0r_1'

theorem one_plus_one_eq_two : 1 + 1 = 2 := by
  rfl

theorem some_calc : 3*(104 - 4)/10 = 30 := by
  rfl

#print some_calc

theorem add_zero' (a : Nat) : a + 0 = a := by
  apply Nat.add_zero



def s : String := "Hello"

#print s






-- Using rfl

theorem eq_refl_1 (x : Nat) : x = x := by
  rfl

theorem eq_refl_2 (x : Nat) : 8 * (x ^ 2) - 5 = 8 * (x ^ 2) - 5 := by
  rfl




-- Using exact

theorem exact_1 (x : Nat) (h : x = 7) : x = 7 := by
  exact h

theorem exact_1' (x : Nat) (h : x = 7) : x = 7 := by
  assumption




-- Using rw

theorem rewrite_1 (x y : Nat) (h : y = x - 2) : 3 * y = 3 * (x - 2) := by
  rw[h]

theorem rewrite_1' (x y : Nat) (h : y = x - 2) : 3 * y = 3 * (x - 2) := by
  rw[← h]

theorem rewrite_2 (x y z : Nat) (h1 : x = 3 * y) (h2 : y = z + 3) : x = 3 * (z + 3) := by
  rw[h1]
  rw[h2]

theorem rewrite_2' (x y z : Nat) (h1 : x = 3 * y) (h2 : y = z + 3) : x = 3 * (z + 3) := by
  rw[h2] at h1
  exact h1

theorem rewrite_2'' (x y z : Nat) (h1 : x = 3 * y) (h2 : y = z + 3) : x = 3 * (z + 3) := by
  rw[← h2]
  exact h1

#print rewrite_2''


-- Defining Nat on our own

namespace Hidden

inductive Natl where
 | zero : Natl
 | succ : Natl → Natl
 deriving Repr

namespace Natl



-- Defining addition on our own

def add (m n : Natl) : Natl :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

instance : Add Natl where
  add := add



-- Proving basic addition lemmas from addition definition

theorem add_zero (m : Natl) : m + zero = m := rfl
theorem add_succ (m n : Natl) : m + succ n = succ (m + n) := rfl



-- Proving addition theorems using induction

theorem zero_add (m : Natl) : zero + m = m := by
  induction m with
  | zero => rfl
  | succ n h => rw[add_succ, h]

theorem succ_add (m n : Natl) : (succ m) + n = succ (m + n) := by
  induction n with
  | zero => rw[add_zero, add_zero]
  | succ n h => rw[add_succ, add_succ, h]

theorem add_comm (m n : Natl) : m + n = n + m := by
  induction n with
  | zero => rw[add_zero, zero_add]
  | succ n h => rw[add_succ, succ_add, h]

theorem add_assoc (p q r : Natl) : p + q + r = p + (q + r) := by
  induction r with
  | zero => rw[add_zero, add_zero]
  | succ r h => rw[add_succ, add_succ, add_succ, h]

end Natl

end Hidden




#check Nat.add_zero
#check Nat.zero_add
#check Nat.add_comm
#check Nat.add_assoc
#check Nat.add_right_cancel




-- Using in-built theorems in Mathlib

theorem adding_zero_1 (a b : Nat) : a + (b + 0) = a + b := by
  rw[Nat.add_zero]

theorem adding_zero_2 (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw[Nat.add_zero]
  rw[Nat.add_zero]

theorem adding_zero_2' (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw[Nat.add_zero, Nat.add_zero]

theorem adding_zero_3 (a b c : Nat) : a + (b + 0) + (c + 0) = a + (b + 0) + c := by
  rw[Nat.add_zero, Nat.add_zero]

theorem adding_zero_3' (a b c : Nat) : a + (b + 0) + (c + 0) = a + (b + 0) + c := by
  repeat rw[Nat.add_zero]



-- Using nth_rw

theorem adding_zero_3'' (a b c : Nat) : a + (b + 0) + (c + 0) = a + (b + 0) + c := by
  nth_rw 2 [Nat.add_zero]




-- Using apply

theorem apply_1 (x y : Nat) (h1 : x = 8) (h2 : x = 8 → y = 3) : y = 3 := by
  apply h2
  exact h1



-- Using have

theorem have_1 (x y : Nat) (h1 : x = 8) (h2 : x = 8 → y = 3) : y = 3 := by
  have h3 : y = 3 := h2 h1
  exact h3



-- Using intro

theorem intro_1 (x y : Nat) : x + 1 = y + 1 → x = y := by
  intro h
  exact Nat.add_right_cancel h



-- Using not equals

theorem not_equals (x : Nat) (h1 : x ≠ 3) : x + 4 ≠ 7 := by
  intro h2
  have h3 := @Nat.add_right_cancel x 4 3
  have h4 := h3 h2
  exact h1 h4




#check mul_comm
#check mul_assoc
#check mul_add
#check add_mul
#check two_mul




section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a*a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

end




-- Groups in Lean

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_inv_cancel' (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel', one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

end MyGroup

end



section

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- Try this.
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  exact lt_trans (lt_of_lt_of_le (lt_of_le_of_lt h₀ h₁) h₂) h₃

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']




-- Just to show some of the various theorems

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

end




example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)



theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by
      apply mul_le_mul
      linarith
      linarith
      apply abs_nonneg
      apply abs_nonneg
    _ < 1 * ε := by
      apply mul_lt_mul
      linarith
      linarith
      exact epos
      linarith
    _ = ε := by apply one_mul



-- Upper and Lower Bounds

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x




section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  apply nnf
  apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp
  apply mul_le_mul
  apply hfa
  apply hgb
  apply nng
  exact nna

end




-- Existential Quantifier

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num





def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a




theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

theorem fnLb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnLb f a) (hgb : FnLb g b) :
    FnLb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

theorem fnUb_mul_left {f : ℝ → ℝ} {a c : ℝ} (hfa : FnUb f a) (h : 0 ≤ c) :
    FnUb (fun x ↦ c * f x) (c * a) :=
  fun x ↦ mul_le_mul_of_nonneg_left (hfa x) (h)

theorem fnUb_mul_left2 {f : ℝ → ℝ} {a c : ℝ} (hfa : FnUb f a) (h : 0 ≤ c) :
    FnUb (fun x ↦ c * f x) (c * a) := by
  intro x
  apply mul_le_mul_of_nonneg_left
  apply hfa x
  apply h





section
variable {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  use d + e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  match divab, divac with
  | ⟨d,beq⟩, ⟨e,ceq⟩ =>
    rw [beq,ceq]
    use d + e; ring

end




def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε




theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos
