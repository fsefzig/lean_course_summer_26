import lecture5.examples5

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.

/-
lemma modulo_eq_rest (n m k r : ℤ) (hn : n ≠ 0) (hr : 0 ≤ r ∧ r < n.natAbs) (h : m = n * k + r)
  : m % n = r := by
  apply (Int.emod_eq_iff hn).mpr
  refine ⟨hr.1, hr.2, ?_⟩
  simp only [h, sub_add_cancel_right, dvd_neg, dvd_mul_right]
-/



--def q (n : ℤ) : ℤ → ℤ_mod n := Quotient.mk (ℤ_mod_setoid n)
--aka, you send n to its equivalence class



--so basically its just asking if m1 and m2 belong to the same equivalence class
--then theyre the same modulo

#check Int.modEq_iff_dvd


--remember we defined x ~ y if n | x-y
lemma exercise0 {n m1 m2 : ℤ} : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  --uhh i removed the hn : n≠0 because it appears my code works fine without it?
  simp only [q, ℤ_mod_setoid]
  refine Eq.to_iff ?_
  refine iff_iff_eq.mp ?_
--def mod_relation (n : ℤ) : ℤ → ℤ → Prop := fun m1 m2 => n ∣ m1 - m2
--scoped notation:50 m1 " ∼[" n "] " m2 => mod_relation n m1 m2
  have h1 : (⟦m1⟧ : Quotient (ℤ_mod_setoid n))= ⟦m2⟧ ↔ n ∣ m1-m2 := by
            --idk why notations like this ^^, since [[m1]]= [[m2]] gave error
    rw [Quotient.eq]
    rfl
  have h2 : n ∣ m1-m2 ↔ m1 % n = m2 % n := by
    rw [← Int.modEq_iff_dvd]
    exact Iff.symm { mp := fun a ↦ id (Eq.symm a), mpr := fun a ↦ id (Int.ModEq.symm a) }
  exact Iff.trans h1 h2


/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/

lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro h
    have hx : x ∈ {z : α | R x z} := by
      --transitive property of the equivalence R
      exact hR.refl x
    have hy : x ∈ {z : α | R y z} := by
      rw[h.symm]
      exact hx
    exact hR.symm hy
    --then, x ∈ set means R x y is true, done
  · intro hRxy
    apply Set.Subset.antisymm_iff.mpr -- show both inclusions
    constructor--hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
    · intro z hin
      exact hR.trans (hR.symm hRxy) hin--omg turned 6 lines into one here
      /-
      have hxz : R x z := hin

      have hRyx : R y x := hR.symm hRxy

      exact hR.trans hRyx hxz
      -/
    · intro z hin
      exact hR.trans hRxy hin


#check Quotient.lift

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
--note: double brackets = equivalence classes


-- idea of this:
-- imagine we have a function f` : X -> Y
-- and we want to have f : X/r -> Y

--where with equivalence classes
--you have like f([x]_n) is always the same


--fix k
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
--           this is X/r ^^
  intro x
  refine Quotient.lift (fun x => (⟦k * x⟧ : ℤ_mod n)) ?_ x
  --no idea whats going on here tbh (well i sorta get it but not rlly)
  intro a b heq
  apply Quotient.sound
  have hdiv : n ∣ a-b := by
    exact heq
  have hkdiv : n ∣ (k * a - k * b ) := by
    rw[← mul_sub]
    apply Dvd.dvd.mul_left hdiv
  exact hkdiv

-- to apply Quotient lift, we need the f`, from Z -> Z/n (all of Z)
-- and that if x~y under the equivalence condition
-- then f(x)=f(y)

-- or in this case, mul_k(x) = mul_k(y)

--note that its a function of k -> [k*x]







-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
    intro a b
    contrapose!
    intro hneq hfeq
    have hg : g (f (a)) =g (f (b)) := by
      exact (congrArg g ∘ fun a ↦ hfeq) α
      --in english: since f(a)=f(b)
    rw[h b] at hg
    rw[h a] at hg
    contradiction



  --for all x, g(f(x))=x
  --suppose f(x)=y
  --then, g(y)=x

  --note: a ≠ b -> f(a)≠f(b)
      --why? suppose a≠b and f(a)=f(b), then g(f(a))=g(f(b))-> a=b

  --contrapositive of this


-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
    intro y
    let x := g (y)
    have hfun : f (x) = y := by
      simp only [x]
      exact h y
    use x


  -- y -> g(y) -> f(g(y))=y

  --for all y, exists x st f(x)=y, use x=g(y)


-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
--
lemma lemma0 {k n : ℤ} (hk : Int.natAbs k < n.natAbs) (hdiv : n ∣ k) : k = 0 := by
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hk
  --useless but motivation so keeping it

#check Int.emod_lt

--Int.emod_lt (a : ℤ) {b : ℤ} (h : b ≠ 0) : a % b < ↑b.natAbs
--def q_res (n : ℤ) : Fin n.natAbs → ℤ_mod n := fun i => q n i.val
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  constructor
  · intro i j hij
    have hi : i< n.natAbs := by
      exact i.isLt
    have hj : j< n.natAbs := by
      exact j.isLt
    simp only [q_res] at hij
    have hdiv : n ∣ ((i.val : ℤ) - (j.val : ℤ)) := by
      exact q_eq.mp hij
    have hless : ((i.val : ℤ) - (j.val : ℤ)).natAbs < n.natAbs := by
      omega
    have halmost : (i.val : ℤ) - (j.val : ℤ) = 0 := by
      --exact lemma0 hn hless hdiv
      exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hless
    omega
    --if i and j are in the same class
    --then n | i-j
    --and since both are smaller than n
    --their difference will be smaller than n
    --so it must be 0
  · intro x
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x

    let y : ℤ := a % n

    use ⟨y.natAbs, ?_⟩
    · sorry
      --idk
    simp [y]
    have h0 : 0 ≤ a % n := Int.emod_nonneg a hn
    have hlt : a % n < (n.natAbs : ℤ) := Int.emod_lt a hn
    omega

lemma Bezout {a b : ℕ} : ∃ k l : ℤ, a * k + b * l = 1 := by
  sorry

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  --chats hint was bezouts

  obtain ⟨k, l, hkl⟩ := Bezout (a := a) (b := b)
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2

  have hstep1 : c*(a*k + b*l) = c := by
    ring -- WHY DOESN"T RING WORK HERE????
    sorry

  have hstep2 : c*a*k + c*b*l = c := by
    calc
    c*a*k + c*b*l = c*(a*k + b*l) := by ring
    _ = c := hstep1

  have hstep3 : a*b*(m*k+n*l) = c := by
    calc
    a*b*(m*k+n*l) = a*b*m*k+a*b*n*l := by ring
    _ = b*m*a*k + a*n*b*l := by ring
    _ = c*a*k + a*n*b*l := by simp [← hm.symm]
    _ = c*a*k + c*b*l := by simp [← hn.symm]
    _ = c := hstep2

  by_cases hc0 : c=0
  · exact Nat.modEq_zero_iff_dvd.mp (congrFun (congrArg HMod.hMod hc0) (a * b))
    --everything divides 0, this is boring
  · have ha : a≥0 := by
      exact Nat.zero_le a
    have hb : b≥0 := by
      exact Nat.zero_le b
    have hab : a*b ≥0 := by
      exact Nat.zero_le (a * b)

    by_cases hc : c>0

    · have hmknl : (m*k+n*l) ≥0 := by
        sorry
      sorry

    · have hc : c≤0 := by
        exact Nat.le_of_not_lt hc
      sorry
    --ok i'm giving up
    --there's so many tedious things
    --like i have to seperate out a≠0, etc etc
    --i might finish writing it up sometime
    --the idea should be there though
    --it's also very not how you intended us to solve it
    --     ¯\_(ツ)_/¯


  --it's about here that i realized my amazing plan
  --failed because mk + nl is in Z and not N
  --and furthermore cannot be guaranteed at all to be in Z

  --uhh wait
  --do (mk+nl) if >0, -(mk+nl) if <0


  --gcd = 1 -> exists k, l in Z st ak +bl =1
  -- -> c(ak+bl)=c
  -- -> have c=an, c=bm
  -- -> bm*ak+ an*bl
