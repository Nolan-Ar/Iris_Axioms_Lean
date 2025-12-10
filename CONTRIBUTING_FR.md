# Contribuer à IRIS Axioms

Merci de votre intérêt pour contribuer au projet IRIS Axioms ! Ce document fournit des directives et les meilleures pratiques pour contribuer.

## Table des Matières

1. [Pour Commencer](#pour-commencer)
2. [Flux de Développement](#flux-de-développement)
3. [Standards de Code](#standards-de-code)
4. [Directives pour les Preuves](#directives-pour-les-preuves)
5. [Documentation](#documentation)
6. [Tests](#tests)
7. [Processus de Pull Request](#processus-de-pull-request)

## Pour Commencer

### Prérequis

Avant de contribuer, assurez-vous d'avoir :
- Lean 4 (v4.24.0) installé via elan
- Git configuré sur votre machine
- VS Code avec l'extension Lean 4 (recommandé)
- Compréhension de base de la syntaxe Lean 4 et de la démonstration de théorèmes

### Configuration de l'Environnement de Développement

1. Forkez le dépôt sur GitHub
2. Clonez votre fork localement :
   ```bash
   git clone https://github.com/VOTRE_NOM_UTILISATEUR/Iris_Axioms_Lean.git
   cd Iris_Axioms_Lean
   ```
3. Ajoutez le dépôt upstream :
   ```bash
   git remote add upstream https://github.com/Nolan-Ar/Iris_Axioms_Lean.git
   ```
4. Installez les dépendances :
   ```bash
   lake update
   lake build
   ```

## Flux de Développement

### Créer une Nouvelle Fonctionnalité ou Correction

1. **Synchroniser avec upstream** :
   ```bash
   git fetch upstream
   git checkout main
   git merge upstream/main
   ```

2. **Créer une branche de fonctionnalité** :
   ```bash
   git checkout -b feature/nom-de-votre-fonctionnalite
   ```
   Utilisez des noms de branches descriptifs :
   - `feature/add-xyz` pour les nouvelles fonctionnalités
   - `fix/description-du-bug` pour les corrections de bugs
   - `docs/ce-que-vous-documentez` pour la documentation
   - `refactor/ce-que-vous-refactorisez` pour le refactoring

3. **Effectuez vos modifications** en suivant les standards de code ci-dessous

4. **Vérifiez vos modifications** :
   ```bash
   lake build
   ```

5. **Committez vos modifications** :
   ```bash
   git add .
   git commit -m "Brève description des changements"
   ```

## Standards de Code

### Conventions de Nommage

- **Types et Structures** : Utilisez `CamelCase`
  ```lean
  structure CompteUtilisateur where
  structure NFT where
  ```

- **Définitions et Théorèmes** : Utilisez `snake_case`
  ```lean
  def calculer_total : ℝ → ℝ := ...
  theorem conservation_monetaire : ...
  ```

- **Axiomes** : Préfixe avec `A` suivi du numéro
  ```lean
  axiom A1_unicite_bijective : ...
  axiom A2_absence_emission_dette : ...
  ```

### Structure du Code

1. **Imports** : Groupez les imports de manière logique
   ```lean
   import Mathlib.Data.Real.Basic
   import Mathlib.Tactic
   import IrisAxioms.iris_axioms
   ```

2. **Namespace** : Utilisez des namespaces appropriés
   ```lean
   namespace IrisAxioms
   -- Votre code ici
   end IrisAxioms
   ```

3. **Sections** : Utilisez des commentaires de documentation pour organiser le code
   ```lean
   /-!
   # Titre de la Section
   Brève description du contenu de cette section
   -/
   ```

### Qualité du Code

- **Pas de `sorry`** : Toutes les preuves doivent être complètes
- **Sûreté de Type** : Exploitez le système de types de Lean
- **Invariants** : Utilisez les champs de structure pour encoder les invariants
  ```lean
  structure Valeurs where
    S : ℝ
    hS : 0 ≤ S  -- Invariant : S est non-négatif
  ```

## Directives pour les Preuves

### Écrire des Preuves

1. **Clarté plutôt que Brièveté** : Préférez les preuves lisibles
   ```lean
   -- Bon : Étapes claires
   theorem exemple : P → Q := by
     intro h
     apply un_lemme
     exact h

   -- Acceptable pour les cas simples
   theorem exemple : P → Q := un_lemme
   ```

2. **Utilisez les Tactiques Appropriées** :
   - `norm_num` pour le raisonnement numérique
   - `simp` pour la simplification
   - `omega` pour l'arithmétique linéaire
   - `constructor` pour construire des structures
   - `cases` pour le pattern matching

3. **Commentez les Preuves Complexes** :
   ```lean
   theorem resultat_complexe : ... := by
     -- Étape 1 : Établir le cas de base
     have h1 : ... := ...
     -- Étape 2 : Utiliser l'induction sur n
     induction n with
     | zero => ...
     | succ n ih => ...
   ```

### Style de Preuve

- Divisez les longues preuves en lemmes
- Nommez les résultats intermédiaires de manière descriptive
- Utilisez `have` pour les étapes intermédiaires
- Utilisez `calc` pour le raisonnement équationnel :
  ```lean
  calc
    a = b := by ...
    _ = c := by ...
    _ = d := by ...
  ```

## Documentation

### Commentaires de Code

1. **Documentation au Niveau du Module** :
   ```lean
   /-
   Module : iris_axioms.lean
   Description : Axiomes IRIS fondamentaux et structures de base
   Auteur : [Votre Nom]
   Date : AAAA-MM-JJ
   -/
   ```

2. **Commentaires de Section** :
   ```lean
   /-!
   # Conservation Monétaire
   Cette section définit l'axiome de conservation monétaire et les théorèmes associés.
   -/
   ```

3. **Documentation de Fonction/Théorème** :
   ```lean
   /--
   Calcule le revenu de base universel pour une période donnée.

   - `V_on` : Valeur totale créée
   - `rho` : Taux de réserve (0 ≤ ρ ≤ 0.3)
   - `T` : Nombre de périodes
   - `N` : Nombre de bénéficiaires
   -/
   def calculer_RU (V_on : ℝ) (rho : ℝ) (T N : ℕ) : ℝ := ...
   ```

### Langue de Documentation

- **La documentation peut être en français ou en anglais**
- Utilisez un langage clair et concis
- Fournissez des exemples lorsque c'est utile
- Expliquez les concepts économiques pour les non-experts

## Tests

### Ajouter des Exemples

Ajoutez des exemples numériques dans `iris_exemples_numeriques.lean` :

```lean
/-- Exemple : Validation de transaction simple -/
def exemple_transaction_simple : Transaction := {
  montant := 100.0
  signature := Hash.mk "exemple_sig"
  timestamp := 1234567890
  h_montant := by norm_num
}

/-- Vérifier que la transaction est valide -/
theorem exemple_transaction_valide :
    0 < exemple_transaction_simple.montant := by
  norm_num
```

### Liste de Vérification

Avant de soumettre :
- [ ] Tous les fichiers compilent sans erreur : `lake build`
- [ ] Pas de `sorry` dans les preuves
- [ ] Tests/exemples ajoutés pour les nouvelles fonctionnalités
- [ ] Documentation complète
- [ ] Le code suit les conventions de nommage

## Processus de Pull Request

### Avant de Soumettre

1. **Mettre à jour depuis upstream** :
   ```bash
   git fetch upstream
   git rebase upstream/main
   ```

2. **Exécuter une compilation complète** :
   ```bash
   lake clean
   lake build
   ```

3. **Réviser vos modifications** :
   ```bash
   git diff main
   ```

### Soumettre une Pull Request

1. Poussez votre branche vers votre fork :
   ```bash
   git push origin feature/nom-de-votre-fonctionnalite
   ```

2. Allez sur GitHub et créez une Pull Request

3. **Titre de la PR** : Utilisez des titres descriptifs
   - `Add: Description` pour les nouvelles fonctionnalités
   - `Fix: Description` pour les corrections de bugs
   - `Docs: Description` pour la documentation
   - `Refactor: Description` pour le refactoring

4. **Description de la PR** : Incluez :
   - Quels changements ont été effectués
   - Pourquoi les changements étaient nécessaires
   - Numéros d'issues pertinents
   - Tests effectués

### Modèle de PR

```markdown
## Description
Brève description des changements

## Type de Changement
- [ ] Nouvelle fonctionnalité
- [ ] Correction de bug
- [ ] Documentation
- [ ] Refactoring

## Changements Effectués
- Liste des changements spécifiques
- Avec détails

## Tests
- Décrire les tests effectués
- Inclure un exemple d'utilisation si applicable

## Liste de Vérification
- [ ] Le code compile sans erreur
- [ ] Pas de `sorry` dans les preuves
- [ ] Documentation mise à jour
- [ ] Exemples ajoutés (si applicable)
- [ ] Suit les standards de code
```

### Revue de Code

- Soyez ouvert aux commentaires et suggestions
- Répondez rapidement aux commentaires de revue
- Effectuez les modifications demandées dans de nouveaux commits
- Une fois approuvé, les mainteneurs fusionneront votre PR

## Bonnes Pratiques

### Performance

- Évitez les tactiques coûteuses en calcul dans les grandes preuves
- Utilisez `#check` pour vérifier les types avant les preuves complexes
- Mettez en cache les résultats intermédiaires avec `let` ou `have`

### Maintenabilité

- Gardez les fonctions et preuves concentrées et à usage unique
- Extrayez les motifs communs en lemmes
- Maintenez un style cohérent dans tout le fichier

### Collaboration

- Communiquez dans les issues avant de commencer des changements majeurs
- Posez des questions dans les discussions ou issues
- Aidez à réviser les PRs des autres quand possible

## Ressources

- [Documentation Lean 4](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Documentation Mathlib](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

## Questions ?

Si vous avez des questions :
1. Consultez les issues et discussions existantes
2. Demandez dans GitHub Discussions
3. Ouvrez une nouvelle issue avec le label `question`

Merci de contribuer à IRIS Axioms !
