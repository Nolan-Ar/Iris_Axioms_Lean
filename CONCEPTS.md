# CONCEPTS IRIS - Lexique Mathématique et Économique

Ce document explique en détail les concepts économiques du système IRIS et leur formalisation mathématique en Lean 4.

## Table des matières

- [Concepts thermodynamiques](#concepts-thermodynamiques)
- [Coefficients de transformation](#coefficients-de-transformation)
- [Régulation automatique](#régulation-automatique)
- [Mécanismes économiques](#mécanismes-économiques)
- [Exemples concrets](#exemples-concrets)
- [Propriétés mathématiques](#propriétés-mathématiques)

## Concepts thermodynamiques

IRIS modélise l'économie comme un système thermodynamique où l'énergie (travail, argent) se conserve et se transforme.

### Les quatre grandeurs fondamentales

| Terme IRIS | Structure Lean | Contrainte | Signification économique |
|------------|----------------|------------|--------------------------|
| **Verum (V)** | `Valeurs.V : ℝ` | `V ≥ 0` | **Valeur vivante** : Actifs productifs en circulation |
| **Dette (D)** | `Valeurs.D : ℝ` | `D ≤ 0` | **Engagement thermique** : Dette créée lors de la production |
| **Stipulat (S)** | `Valeurs.S : ℝ` | `S ≥ 0` | **Preuve d'effort** : Énergie dépensée, travail accompli |
| **Unum (U)** | `Valeurs.U : ℝ` | `U ≥ 0` | **Monnaie d'usage** : Moyen d'échange périssable |

### Conservation thermodynamique (Axiome A1)

```lean
axiom A1_conservation : ∀ (v : Valeurs), v.S + v.U + v.V + v.D = 0
```

**Interprétation** :
- La somme algébrique des quatre grandeurs est toujours nulle
- Toute création de valeur (V > 0) génère une dette égale (D < 0)
- L'énergie dépensée (S) et les paiements (U) compensent exactement
- **Analogie physique** : Premier principe de la thermodynamique (conservation de l'énergie)

### Décomposition de V (Axiome A2)

```lean
axiom A2_decomposition_V : ∀ (sys : SystemState),
  sys.V_total = sys.V_on + sys.V_immo
```

- **V_on** : Valeur "en marche" (in the money), active et liquide
- **V_immo** : Valeur immobilisée (patrimoine, CNP)

**Exemple** :
- Alice possède 1000€ en banque (V_on) + une maison valant 200,000€ (V_immo)
- V_total = 1000 + 200,000 = 201,000€

## Coefficients de transformation

### η - Coefficient de création de valeur (Axiome A18)

```lean
structure CoefficientsCreation where
  eta : ℝ
  psi : ℝ
  h_eta : 0 < eta ∧ eta ≤ 2
  h_psi : 0 < psi ∧ psi ≤ 1
```

**Formule de création** :
```
ΔV = η × ψ × E
```

Où :
- **ΔV** : Variation de valeur créée
- **η** : Efficacité de transformation énergie → valeur
- **ψ** : Facteur de qualité (0 < ψ ≤ 1)
- **E** : Énergie dépensée (temps × argent)

### Décomposition de η

```
η = η_phys × μ_social
```

| Composante | Plage | Signification |
|------------|-------|---------------|
| **η_phys** | (0, 1] | **Efficacité physique** : Rendement technique du processus |
| **μ_social** | [1, 2] | **Multiplicateur social** : Impact social de l'activité |

**Exemples** :
1. **Industrie polluante** : η_phys = 0.9 (très efficace), μ_social = 1.0 (impact neutre) → η = 0.9
2. **École publique** : η_phys = 0.6 (coût élevé), μ_social = 1.8 (fort impact social) → η = 1.08
3. **Startup tech** : η_phys = 0.8, μ_social = 1.5 → η = 1.2

### κ - Coefficient de conversion U → V (Axiome A5)

```lean
axiom A5_conversion_U_V : ∀ (cu : CompteUtilisateur) (montant_U : ℝ),
  0 ≤ montant_U →
  ∃ (kappa : ℝ), 0 < kappa ∧ kappa ≤ 1 ∧
  (cu with wallet_V := cu.wallet_V + kappa * montant_U,
           wallet_U := cu.wallet_U - montant_U).wallet_V ≥ 0
```

**Interprétation** :
- κ représente le taux de change U → V
- 1 Unum (U) converti donne κ Verum (V)
- κ ≤ 1 car U est périssable (perte de valeur)
- **Exemple** : Avec κ = 0.95, convertir 100U donne 95V

### ρ - Taux de rétention UBI (Axiome A13)

```lean
axiom A13_perissabilite_U : ∀ (U_t : ℝ) (rho : ℝ),
  0 ≤ rho ∧ rho < 1 →
  let U_next := (1 - rho) * U_t
  U_next < U_t
```

**Péremption de U** :
- Chaque cycle, une fraction ρ de U disparaît
- Encourage la circulation rapide
- **Exemple** : Avec ρ = 0.05 (5% par mois), 100U devient 95U après un mois

## Régulation automatique

### Thermomètre économique (Axiome A19)

```lean
def thermometre (rad : RAD) : ℝ := rad.D_total / rad.V_on_total
```

**Zones de température** :

```
r_t = D_total / V_on_total

┌─────────────────────────────────────────────────────┐
│  r_t < 0.85         │  "FROID"  │  Déflation        │
│  ────────────────────────────────────────────────── │
│  0.85 ≤ r_t ≤ 1.15  │  ÉQUILIBRE │  Stable          │
│  ────────────────────────────────────────────────── │
│  r_t > 1.15         │  "CHAUD"   │  Inflation       │
└─────────────────────────────────────────────────────┘
```

**Interprétation** :
- **r_t < 0.85** : Trop de valeur (V) par rapport à la dette (D) → Déflation → Augmenter η
- **0.85 ≤ r_t ≤ 1.15** : Équilibre sain
- **r_t > 1.15** : Trop de dette (D) par rapport à V → Inflation → Réduire η

### Ajustement automatique de η (Axiome A20)

```lean
axiom A20_ajustement_eta : ∀ (rad_before rad_after : RAD),
  let r_t := thermometre rad_before
  (r_t > 1.15 → rad_after.eta < rad_before.eta) ∧
  (r_t < 0.85 → rad_after.eta > rad_before.eta) ∧
  (0.85 ≤ r_t ∧ r_t ≤ 1.15 → rad_after.eta = rad_before.eta)
```

**Mécanisme de feedback** :
1. Mesurer r_t à chaque cycle
2. Si r_t > 1.15 (surchauffe) : Réduire η de 5-10% → Moins de création de valeur
3. Si r_t < 0.85 (refroidissement) : Augmenter η de 5-10% → Plus de création
4. Sinon : Maintenir η stable

**Exemple numérique** :
```lean
-- État initial : surchauffe
let rad_before : RAD := {
  D_total := 150000,
  V_on_total := 100000,  -- r_t = 1.5 > 1.15
  eta := 1.2,
  ...
}

-- Ajustement automatique : η ↓
let rad_after : RAD := {
  D_total := 150000,
  V_on_total := 100000,
  eta := 1.08,  -- Réduit de 10%
  ...
}
```

## Mécanismes économiques

### Distribution du Revenu Universel (Axiome A12)

```lean
axiom A12_distribution_RU :
  ∀ (beneficiaires : List CompteUtilisateur)
    (allocation : CompteUtilisateur → ℝ)
    (U_t : ℝ),
  0 ≤ U_t →
  (beneficiaires.attach.map (fun ⟨cu, _⟩ => allocation cu)).sum = U_t
```

**Fonctionnement** :
1. Chaque cycle, un montant U_t est distribué
2. Chaque bénéficiaire reçoit une allocation
3. La somme des allocations = U_t exactement (conservation)

**Formule de calcul** :
```
U_t = (1 - ρ) × V_on_total / (12 × 1000)
```

Où :
- ρ : Taux de rétention (ex: 0.05)
- V_on_total : Valeur totale en circulation
- Division par 12 : Distribution mensuelle
- Division par 1000 : Normalisation

**Exemple** :
- V_on_total = 1,000,000€
- ρ = 0.05
- U_t = (1 - 0.05) × 1,000,000 / (12 × 1000) = 79.17€ par mois par personne

### TAP - Trésorerie Avance Payroll (Axiome A21)

```lean
axiom A21_capacite_TAP : ∀ (ce : CompteEntrepriseEtendu),
  let reserve := ce.tresorerie_V + (ce.NFT_financiers.map (·.valeur)).sum
  let tap_total := (ce.TAP_en_cours.map (·.montant_avance)).sum
  tap_total ≤ 0.8 * reserve
```

**Règle de prudence** :
- Une entreprise peut avancer jusqu'à 80% de ses réserves
- Réserves = trésorerie V + NFT financiers
- Limite l'effet de levier
- Évite la faillite en cascade

**Exemple** :
```lean
-- Entreprise avec réserves
let entreprise : CompteEntrepriseEtendu := {
  tresorerie_V := 50000,
  NFT_financiers := [nft1, nft2],  -- Valeur totale : 30000
  TAP_en_cours := [tap1, tap2],     -- Montant total : 60000
  ...
}

-- Vérification
reserve = 50000 + 30000 = 80000
tap_total = 60000
60000 ≤ 0.8 × 80000 = 64000  ✓ Valide
```

### Inviolabilité cryptographique (Axiome A7)

```lean
axiom A7_pas_double_depense : ∀ (cu : CompteUtilisateur) (tx1 tx2 : Transaction),
  ValidSig cu tx1 → ValidSig cu tx2 →
  cu.wallet_V ≥ tx1.montant_V + tx2.montant_V
```

**Protection contre la double dépense** :
- Deux transactions signées valides ne peuvent excéder le solde
- Garantit l'intégrité du système
- Analogie avec Bitcoin : empêche de dépenser deux fois le même argent

## Exemples concrets

### Exemple 1 : Alice crée de la valeur

**Contexte** :
- Alice est développeuse freelance
- Elle travaille 48 heures sur un projet
- Le client paie 80 Unum
- Efficacité : η_phys = 0.8, μ_social = 1.5 → η = 1.2
- Qualité : ψ = 1.0 (excellent travail)

**Calcul de l'énergie** :
```
E = α × temps + β × argent
E = 0.6 × 48 + 0.4 × 80
E = 28.8 + 32
E = 60.8
```

**Création de valeur** :
```
ΔV = η × ψ × E
ΔV = 1.2 × 1.0 × 60.8
ΔV = 72.96 ≈ 73 Verum
```

**En Lean** :
```lean
example : let η := (0.8 : ℝ) * 1.5 in
          let ψ := (1.0 : ℝ) in
          let E := 0.6 * 48 + 0.4 * 80 in
          let ΔV := η * ψ * E in
          ΔV = 72.96 := by
  norm_num
```

### Exemple 2 : Système en déséquilibre

**Scénario de crise** :
```lean
-- État initial : Surchauffe économique
let rad_crise : RAD := {
  D_total := 300000,     -- Dette élevée
  V_on_total := 100000,  -- Valeur faible
  eta := 2.0,            -- Création trop élevée
  kappa := 0.8,
  ...
}

-- Calcul du thermomètre
r_t = 300000 / 100000 = 3.0

-- Diagnostic : r_t = 3.0 > 1.15 → SURCHAUFFE
```

**Réaction automatique** (A20) :
1. Détection : r_t > 1.15
2. Action : Réduire η de 20%
3. Nouveau η : 2.0 × 0.8 = 1.6

```lean
theorem ajustement_crise : ∀ (rad_before rad_after : RAD),
  thermometre rad_before = 3.0 →
  A20_ajustement_eta rad_before rad_after →
  rad_after.eta < rad_before.eta := by
  intro rad_before rad_after h_thermo h_ajust
  have h_surchauffe : thermometre rad_before > 1.15 := by
    rw [h_thermo]
    norm_num
  exact (h_ajust.1 h_surchauffe)
```

### Exemple 3 : Contrat incomplet

**Cas d'usage** : Contrat de livraison avec clauses manquantes

```lean
-- États possibles
inductive Outcome
| delivered_on_time
| delivered_late
| not_delivered

-- Contrat incomplet
def contrat_livraison : PartialContract Outcome := fun ω =>
  match ω with
  | "on_time" => some delivered_on_time
  | "late" => some delivered_late
  | _ => none  -- Non spécifié (grève, catastrophe, etc.)

-- Raffinement du contrat
def contrat_complete : PartialContract Outcome := fun ω =>
  match ω with
  | "on_time" => some delivered_on_time
  | "late" => some delivered_late
  | "strike" => some not_delivered  -- Clause ajoutée
  | _ => some not_delivered         -- Défaut par défaut
```

**Théorème** : Le raffinement préserve les engagements existants
```lean
theorem raffinement_preserving :
  refines_contract contrat_livraison contrat_complete := by
  intro ω h_spec
  cases ω with
  | "on_time" => simp [contrat_livraison, contrat_complete]
  | "late" => simp [contrat_livraison, contrat_complete]
```

## Propriétés mathématiques

### Positivité des quantités

```lean
-- V est toujours positif ou nul
theorem V_non_negative : ∀ (v : Valeurs), 0 ≤ v.V := v.hV

-- S (travail) est positif
theorem S_positive : ∀ (v : Valeurs), 0 ≤ v.S := v.hS

-- U (monnaie) est positif
theorem U_positive : ∀ (v : Valeurs), 0 ≤ v.U := v.hU

-- D (dette) est négatif ou nul
theorem D_non_positive : ∀ (v : Valeurs), v.D ≤ 0 := v.hD
```

### Bornes des coefficients

```lean
-- η est borné
theorem eta_bounds : ∀ (coef : CoefficientsCreation),
  0 < coef.eta ∧ coef.eta ≤ 2 := coef.h_eta

-- κ est dans (0, 1]
theorem kappa_bounds : ∀ (rad : RAD),
  0 < rad.kappa ∧ rad.kappa ≤ 1 := rad.h_kappa

-- μ_social dans [1, 2]
theorem mu_social_bounds : ∀ (μ : ℝ),
  is_valid_mu_social μ → 1 ≤ μ ∧ μ ≤ 2 := by
  intro μ h
  exact h
```

### Conservation et stabilité

```lean
-- Conservation totale
theorem conservation_totale : ∀ (sys : SystemState),
  sys.V_total + sys.D_total + sys.S_total + sys.U_total = 0 := by
  intro sys
  exact sys.h_conservation

-- Stabilité du thermomètre
theorem thermometre_stable : ∀ (rad : RAD),
  let r_t := thermometre rad
  0.85 ≤ r_t ∧ r_t ≤ 1.15 →
  ∀ (rad' : RAD), A20_ajustement_eta rad rad' →
  rad'.eta = rad.eta := by
  intro rad r_t h_equilibre rad' h_ajust
  exact (h_ajust.2.2 h_equilibre)
```

## Comparaison avec d'autres systèmes

| Concept | Système traditionnel | Système IRIS |
|---------|---------------------|--------------|
| **Monnaie** | Unique (Euro, Dollar) | Dual (U périssable, V durable) |
| **Création** | Prêt bancaire avec intérêts | Travail + énergie → valeur |
| **Inflation** | Contrôle par taux directeurs | Auto-régulation par thermomètre |
| **Distribution** | Salaires + prestations | Revenu Universel (UBI) intégré |
| **Dette** | Croissance infinie possible | Bornée par thermomètre |
| **Garanties** | Collatéral physique | Signatures cryptographiques |

## Glossaire technique

- **RAD** : Registre Automatique de Distribution
- **CNP** : Compte Nominal Patrimonial (patrimoine immobilisé)
- **TAP** : Trésorerie Avance Payroll (avance sur salaire)
- **NFT** : Non-Fungible Token (jeton unique avec généalogie)
- **UBI** : Universal Basic Income (Revenu Universel)
- **TU** : Titulaire Utilisateur (identifiant unique)
- **VC** : Vérification Cryptographique (clé publique)

## Références

Pour approfondir, voir :
- [REFERENCES.bib](REFERENCES.bib) - Bibliographie complète
- [README.md](README.md) - Documentation générale
- [IrisAxioms/iris_axioms.lean](IrisAxioms/iris_axioms.lean) - Axiomes formels

---

**Version** : 1.0
**Dernière mise à jour** : 2025-12-09
