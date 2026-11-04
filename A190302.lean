import Mathlib

/-!
# A190302 — « Smallest h such that the decimal expansion of n·h
#             starts with 1 » (Krizek 2011)

Conjecture (Felix Fröhlich, 28 juil. 2018) : `a(n) < 6` pour tout `n`
(vérifiée par Fröhlich jusqu'à `n = 10022141`). La fiche pose aussi
`a(n) = A187285(n) / n` (quotient du plus petit multiple de `n`
commençant par `1`).

Preuve (ici) : pour `d = Nat.log 10 n` (i.e. `10^d ≤ n < 10^{d+1}`) :
- si `n < 2·10^d` (chiffre de tête = 1), `h = 1` convient : `a(n) = 1` ;
- si `2·10^d ≤ n` (chiffre de tête ≥ 2), aucun multiple `n·h < 10^{d+1}`
  ne peut commencer par `1` (il est `≥ n ≥ 2·10^d` tout en restant
  `< 10^{d+1}`), et le premier multiple `≥ 10^{d+1}` tombe dans
  `[10^{d+1}, 10^{d+1} + n) ⊆ [10^{d+1}, 2·10^{d+1})` puisque `n < 10^{d+1}` ;
  donc `a(n) = ⌈10^{d+1} / n⌉ = (10^{d+1} + n − 1)/n`, qui vaut au plus
  `⌈10^{d+1} / (2·10^d)⌉ = 5`.

Antériorité : la borne `a(n) ≤ 5` est assertée sans preuve dans les
commentaires d'A187285 (Greathouse 2011) ; présente formalisation =
première preuve écrite et première formalisation connues [T-Lean].

Contenu du fichier :
- `startsWithOne m` : « `m` commence par le chiffre `1` », forme
  encadrement `∃ k, 10^k ≤ m < 2·10^k` (rédaction canonique validée
  par oracle — voir `A190302/VERIFICATIONS/`) ;
- `startsWithOne_iff_getLastD` : fidélité — équivalence avec la lecture
  littérale OEIS via `Nat.digits` (chiffre le plus significatif = 1) ;
- `a190302 n` : `sInf {h | 1 ≤ h ∧ startsWithOne (n·h)}` — `0` par
  convention sur ensemble vide (`n = 0`), totalisant ;
- `a190302_eq_one` / `a190302_eq_ceilDiv` : la formule exacte par cas ;
- `A190302` : `1 ≤ a190302 n ∧ a190302 n < 6` pour `n ≥ 1` — la clause
  `1 ≤` exclut la vacuité (`sInf ∅ = 0 < 6` serait un faux positif) ;
- `A190302_lt_six` : corollaire verbatim de la conjecture ;
- onze valeurs de la fiche vérifiées ponctuellement (spot-check).
-/

section A190302

/-- « l'écriture décimale de `m` commence par le chiffre `1` » :
    `m ∈ [10^k, 2·10^k)` pour un `k` — le chiffre le plus
    significatif vaut `1`. Faux pour `m = 0`. -/
def startsWithOne (m : ℕ) : Prop := ∃ k : ℕ, 10 ^ k ≤ m ∧ m < 2 * 10 ^ k

/-- Décomposition `m = reste + 10^{L−1}·(chiffre de tête)`, où
    `L = (Nat.digits 10 m).length` et le chiffre de tête est le
    dernier élément de `Nat.digits 10 m` (liste little-endian). -/
theorem ofDigits_dropLast_add_getLast {m : ℕ}
    (hne : Nat.digits 10 m ≠ []) :
    m = Nat.ofDigits 10 (Nat.digits 10 m).dropLast
      + 10 ^ ((Nat.digits 10 m).length - 1) *
        (Nat.digits 10 m).getLast hne := by
  have h1 : Nat.digits 10 m = (Nat.digits 10 m).dropLast ++
      [(Nat.digits 10 m).getLast hne] :=
    (List.dropLast_concat_getLast hne).symm
  conv_lhs => rw [← Nat.ofDigits_digits 10 m, h1]
  rw [Nat.ofDigits_append, List.length_dropLast, Nat.ofDigits_singleton]

/-- **Fidélité** : `startsWithOne m` équivaut à « le chiffre le plus
    significatif de `m` en base 10 vaut `1` », lu littéralement sur
    `Nat.digits` (dernier élément de la liste, `0` sur liste vide). -/
theorem startsWithOne_iff_getLastD {m : ℕ} :
    startsWithOne m ↔ (Nat.digits 10 m).getLastD 0 = 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · constructor
    · rintro ⟨k, hk, -⟩
      have : 0 < 10 ^ k := by positivity
      omega
    · intro h
      have hz : (Nat.digits 10 0).getLastD 0 = 0 := by simp
      omega
  have hne : Nat.digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  have hDg : (Nat.digits 10 m).getLastD 0
      = (Nat.digits 10 m).getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  rw [hDg]
  constructor
  · -- `10^k ≤ m < 2·10^k` → chiffre de tête `d` vérifie `d·10^k ≤ m`,
    -- donc `d < 2`, et `d ≥ 1` (chiffre de tête non nul) : `d = 1`.
    rintro ⟨k, hkm, hmk⟩
    have hlog : Nat.log 10 m = k := by
      apply Nat.log_eq_of_pow_le_of_lt_pow hkm
      calc m < 2 * 10 ^ k := hmk
        _ < 10 ^ (k + 1) := by
          rw [pow_succ]
          have : 0 < 10 ^ k := by positivity
          omega
    have hlen : (Nat.digits 10 m).length = k + 1 := by
      rw [Nat.length_digits 10 m (by norm_num) hm, hlog]
    have hdpos : 1 ≤ (Nat.digits 10 m).getLast hne :=
      Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 10 hm)
    have hmval := ofDigits_dropLast_add_getLast hne
    rw [hlen] at hmval
    simp only [Nat.add_sub_cancel] at hmval
    have hd2 : (Nat.digits 10 m).getLast hne < 2 := by
      rcases lt_or_ge ((Nat.digits 10 m).getLast hne) 2 with hlt | hge2
      · exact hlt
      · exfalso
        have h1 : 2 * 10 ^ k
            ≤ 10 ^ k * (Nat.digits 10 m).getLast hne := by
          calc 2 * 10 ^ k = 10 ^ k * 2 := by rw [mul_comm]
            _ ≤ 10 ^ k * (Nat.digits 10 m).getLast hne :=
              Nat.mul_le_mul (le_refl _) hge2
        omega
    omega
  · -- chiffre de tête `= 1` → `m = reste + 10^{L−1}` avec
    -- `reste < 10^{L−1}` → `m ∈ [10^{L−1}, 2·10^{L−1})`.
    intro hd1
    have hmval := ofDigits_dropLast_add_getLast hne
    rw [hd1, mul_one] at hmval
    have hrest : Nat.ofDigits 10 (Nat.digits 10 m).dropLast
        < 10 ^ ((Nat.digits 10 m).length - 1) := by
      rw [← List.length_dropLast]
      apply Nat.ofDigits_lt_base_pow_length (by norm_num)
      intro x hx
      exact Nat.digits_lt_base (by norm_num) (List.dropLast_subset _ hx)
    exact ⟨(Nat.digits 10 m).length - 1, by omega, by omega⟩

/-- Terme général de la suite : plus petit `h ≥ 1` tel que `n·h`
    commence par `1`. `0` par convention si l'ensemble est vide
    (cas `n = 0`) — totalisant via `sInf` sur `ℕ`. -/
noncomputable def a190302 (n : ℕ) : ℕ :=
  sInf {h : ℕ | 1 ≤ h ∧ startsWithOne (n * h)}

/-- Cas « chiffre de tête `= 1` » (`10^d ≤ n < 2·10^d`) : `a(n) = 1`. -/
theorem a190302_eq_one_of_pow {n d : ℕ}
    (h1 : 10 ^ d ≤ n) (h2 : n < 2 * 10 ^ d) :
    a190302 n = 1 := by
  have h1mem : (1 : ℕ) ∈ {h : ℕ | 1 ≤ h ∧ startsWithOne (n * h)} := by
    refine ⟨le_rfl, d, ?_⟩
    rw [mul_one]
    exact ⟨h1, h2⟩
  apply le_antisymm
  · exact Nat.sInf_le h1mem
  · exact (Nat.sInf_mem ⟨1, h1mem⟩).1

/-- Cas « chiffre de tête `≥ 2` » (`2·10^d ≤ n < 10^{d+1}`) :
    `a(n) = ⌈10^{d+1} / n⌉`. Le premier multiple de `n` qui atteint
    `10^{d+1}` est `n·⌈10^{d+1}/n⌉ ∈ [10^{d+1}, 10^{d+1} + n)` —
    donc commence par `1` ; aucun `h` plus petit n'atteint `10^{d+1}`
    et aucun multiple `< 10^{d+1}` ne commence par `1` (il est
    `≥ 2·10^d`). -/
theorem a190302_eq_ceilDiv_of_pow {n d : ℕ}
    (h2 : 2 * 10 ^ d ≤ n) (hn : n < 10 ^ (d + 1)) :
    a190302 n = 10 ^ (d + 1) ⌈/⌉ n := by
  have hnpos : 0 < n := by
    have : 0 < 10 ^ d := by positivity
    omega
  set c := (10 ^ (d + 1)) ⌈/⌉ n with hc
  -- `10^{d+1} ≤ n·c` : définition du plafond (connexion de Galois)
  have hnc : 10 ^ (d + 1) ≤ n * c :=
    (ceilDiv_le_iff_le_mul hnpos).mp le_rfl
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hnc
      have : 0 < 10 ^ (d + 1) := by positivity
      omega
    · exact h0
  -- `n·c ≤ 10^{d+1} + n − 1 < 2·10^{d+1}` car `n < 10^{d+1}`
  have hnc2 : n * c < 2 * 10 ^ (d + 1) := by
    have key : n * c ≤ 10 ^ (d + 1) + n - 1 := by
      rw [hc, Nat.ceilDiv_eq_add_pred_div]
      exact Nat.mul_div_le _ _
    have : 0 < 10 ^ (d + 1) := by positivity
    omega
  have hc_mem : c ∈ {h : ℕ | 1 ≤ h ∧ startsWithOne (n * h)} :=
    ⟨hc1, d + 1, hnc, hnc2⟩
  -- minimalité : tout `h` admissible vérifie `n·h ≥ 10^{d+1}` :
  -- son témoin `k` ne peut être `≤ d` (`n·h ≥ n ≥ 2·10^d`).
  have hmin : ∀ h ∈ {h : ℕ | 1 ≤ h ∧ startsWithOne (n * h)}, c ≤ h := by
    rintro h ⟨hh1, k, hkn, hnk⟩
    have hkd : d + 1 ≤ k := by
      rcases lt_or_ge k (d + 1) with hlt | hge
      · exfalso
        have hk10 : 10 ^ k ≤ 10 ^ d :=
          Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp hlt)
        have hnh : n ≤ n * h := by
          calc n = n * 1 := (mul_one n).symm
            _ ≤ n * h := Nat.mul_le_mul_left _ hh1
        omega
      · exact hge
    have : 10 ^ (d + 1) ≤ n * h :=
      (Nat.pow_le_pow_right (by norm_num) hkd).trans hkn
    exact (ceilDiv_le_iff_le_mul hnpos).mpr this
  apply le_antisymm
  · exact Nat.sInf_le hc_mem
  · exact hmin _ (Nat.sInf_mem ⟨c, hc_mem⟩)

/-- Formule avec `d = Nat.log 10 n` (= nombre de chiffres de `n` moins 1),
    cas chiffre de tête `= 1`. -/
theorem a190302_eq_one {n : ℕ} (hn : 1 ≤ n)
    (h : n < 2 * 10 ^ Nat.log 10 n) : a190302 n = 1 :=
  a190302_eq_one_of_pow (Nat.pow_log_le_self 10 (by omega)) h

/-- Formule avec `d = Nat.log 10 n`, cas chiffre de tête `≥ 2`. -/
theorem a190302_eq_ceilDiv {n : ℕ}
    (hn : 2 * 10 ^ Nat.log 10 n ≤ n) :
    a190302 n = 10 ^ (Nat.log 10 n + 1) ⌈/⌉ n :=
  a190302_eq_ceilDiv_of_pow hn (Nat.lt_pow_succ_log_self (by norm_num) n)

/-- **Conjecture Fröhlich 2018 — PROUVÉE** : `a(n) < 6` pour tout
    `n ≥ 1`. Forme renforcée non-vacue `1 ≤ a(n) < 6` : `a(n)` est un
    vrai témoin (`sInf ∅ = 0` rendrait `< 6` trivial). Dans le cas
    chiffre de tête `≥ 2`, `a(n) = ⌈10^{d+1}/n⌉ ≤ ⌈10^{d+1}/(2·10^d)⌉
    = 5`. -/
theorem A190302 (n : ℕ) (hn : 1 ≤ n) : 1 ≤ a190302 n ∧ a190302 n < 6 := by
  rcases lt_or_ge n (2 * 10 ^ Nat.log 10 n) with h | h
  · rw [a190302_eq_one hn h]; omega
  · rw [a190302_eq_ceilDiv h]
    have hnpos : 0 < n := hn
    set c := 10 ^ (Nat.log 10 n + 1) ⌈/⌉ n
    have hnc : 10 ^ (Nat.log 10 n + 1) ≤ n * c :=
      (ceilDiv_le_iff_le_mul hnpos).mp le_rfl
    -- `⌈10^{d+1}/n⌉ ≤ 5`  ⟺  `10^{d+1} ≤ 5·n`, vrai car `2·10^d ≤ n`
    have hc5 : c ≤ 5 := by
      rw [ceilDiv_le_iff_le_mul hnpos, pow_succ]
      omega
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at hnc
        have : 0 < 10 ^ (Nat.log 10 n + 1) := by positivity
        omega
      · exact h0
    exact ⟨hc1, by omega⟩

/-- Corollaire verbatim de la conjecture OEIS : `a(n) < 6`. -/
theorem A190302_lt_six (n : ℕ) (hn : 1 ≤ n) : a190302 n < 6 :=
  (A190302 n hn).2

/-! ### Vérification ponctuelle — onze valeurs de la fiche (spot-check) -/

example : a190302 1 = 1 :=
  a190302_eq_one_of_pow (d := 0) (by decide) (by decide)
example : a190302 2 = 5 := by
  rw [a190302_eq_ceilDiv_of_pow (d := 0) (by decide) (by decide)]; decide
example : a190302 3 = 4 := by
  rw [a190302_eq_ceilDiv_of_pow (d := 0) (by decide) (by decide)]; decide
example : a190302 4 = 3 := by
  rw [a190302_eq_ceilDiv_of_pow (d := 0) (by decide) (by decide)]; decide
example : a190302 5 = 2 := by
  rw [a190302_eq_ceilDiv_of_pow (d := 0) (by decide) (by decide)]; decide
example : a190302 7 = 2 := by
  rw [a190302_eq_ceilDiv_of_pow (d := 0) (by decide) (by decide)]; decide
example : a190302 11 = 1 :=
  a190302_eq_one_of_pow (d := 1) (by decide) (by decide)
example : a190302 12 = 1 :=
  a190302_eq_one_of_pow (d := 1) (by decide) (by decide)
example : a190302 19 = 1 :=
  a190302_eq_one_of_pow (d := 1) (by decide) (by decide)
example : a190302 20 = 5 := by
  rw [a190302_eq_ceilDiv_of_pow (d := 1) (by decide) (by decide)]; decide
example : a190302 21 = 5 := by
  rw [a190302_eq_ceilDiv_of_pow (d := 1) (by decide) (by decide)]; decide

#print axioms A190302
#print axioms A190302_lt_six

end A190302
