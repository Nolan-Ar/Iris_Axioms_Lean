# IRIS Axioms - Formalisation en Lean 4

Formalisation mathématique des axiomes IRIS (Integrated Resource Information System) en Lean 4, avec preuves vérifiées de cohérence et de propriétés économiques.

## 📋 Description

Ce projet formalise un système économique basé sur :
- **Axiomes fondamentaux** : Conservation monétaire, distribution du revenu universel, inviolabilité
- **Théorie des jeux** : Stratégies, équilibres de Nash, mécanismes d'incitation
- **Contrats incomplets** : Validation partielle, résolution de conflits
- **Échange d'énergie** : Modélisation des flux énergétiques
- **NFTs et généalogie** : Traçabilité cryptographique

## 🚀 Installation rapide

### Prérequis

- **Lean 4** (v4.24.0)
- **Git**
- **curl** (pour elan)
- Au moins **4 GB de RAM** disponible
- **~10 GB d'espace disque** (pour Mathlib et dépendances)

### Installation automatique

```bash
# Cloner le projet
git clone https://github.com/Nolan-Ar/Iris_Axioms_Lean.git
cd Iris_Axioms_Lean

# Lancer le script d'installation
chmod +x setup.sh
./setup.sh
```

### Installation manuelle

#### 1. Installer elan (gestionnaire de versions Lean)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Puis redémarrer votre terminal ou exécuter :
```bash
source ~/.profile  # ou ~/.bashrc selon votre shell
```

#### 2. Vérifier l'installation de Lean

```bash
lean --version  # Devrait afficher : Lean (version 4.24.0, ...)
lake --version  # Lake est l'outil de build de Lean
```

#### 3. Récupérer les dépendances du projet

```bash
lake update
```

#### 4. Compiler le projet

```bash
lake build
```

**Note** : La première compilation peut prendre **20-40 minutes** car Mathlib (la bibliothèque mathématique standard de Lean) doit être compilée.

## 🛠️ Utilisation

### Compiler le projet

```bash
# Compilation complète
lake build

# Ou utiliser le Makefile
make build
```

### Exécuter le programme

```bash
# Lancer l'exécutable principal
lake exe irisaxioms

# Ou
make run
```

Affiche : `IRIS compilé. Toutes les preuves ont été vérifiées`

### Vérifier les preuves

```bash
# Vérifier un fichier spécifique
lean IrisAxioms/iris_axioms.lean

# Nettoyer et recompiler
make clean
make build
```

### Travailler avec VS Code

1. Installer [VS Code](https://code.visualstudio.com/)
2. Installer l'extension **Lean 4** (ID: `leanprover.lean4`)
3. Ouvrir le dossier du projet dans VS Code
4. Les fichiers `.lean` bénéficieront :
   - De la coloration syntaxique
   - Des messages d'erreur en temps réel
   - De l'autocomplétion
   - Des infobulles pour les théorèmes

## 📁 Structure du projet

```
Iris_Axioms_Lean/
├── IrisAxioms/
│   ├── iris_axioms.lean                 # Axiomes fondamentaux IRIS
│   ├── iris_axioms_extended.lean        # Extensions des axiomes
│   ├── iris_theoremes_extended.lean     # Théorèmes avancés
│   ├── iris_brique.lean                 # Briques de base (TU, VC, Hash)
│   ├── iris_game_theory.lean            # Théorie des jeux appliquée
│   ├── iris_incomplete_contracts.lean   # Contrats incomplets
│   ├── iris_energy_exchange.lean        # Échange d'énergie
│   ├── iris_exemples_numeriques.lean    # Exemples et cas pratiques
│   ├── iris_validation_complete.lean    # Validation globale
│   └── validation_correctifs.lean       # Correctifs de validation
├── IrisAxioms.lean                      # Point d'entrée de la bibliothèque
├── Main.lean                            # Programme principal
├── lakefile.lean                        # Configuration Lake (build)
├── lean-toolchain                       # Version de Lean (v4.24.0)
└── README.md                            # Ce fichier
```

## 📚 Modules principaux

### 1. `iris_axioms.lean`
Définit les axiomes fondamentaux :
- **Conservation monétaire** : S + U + V + D = 0
- **Distribution du RU** : Mécanisme de revenu universel
- **Inviolabilité** : Protection cryptographique via signatures

Structures principales :
- `Valeurs` : Grandeurs économiques (S, U, V, D)
- `CompteUtilisateur` : Wallets et patrimoine CNP
- `NFT` : Tokens non-fongibles avec généalogie
- `Transaction` : Transferts de valeur avec preuves

### 2. `iris_game_theory.lean`
Modélise les interactions stratégiques :
- Jeux à deux joueurs
- Équilibres de Nash
- Mécanismes d'incitation
- Théorème de stabilité des équilibres

### 3. `iris_incomplete_contracts.lean`
Gestion des contrats partiellement définis :
- Spécification partielle des clauses
- Mécanismes de résolution de conflits
- Théorème d'exécution partielle valide

### 4. `iris_energy_exchange.lean`
Modélisation des flux énergétiques :
- Conservation de l'énergie
- Équivalence énergie-monnaie
- Efficacité des transferts

## 🧪 Exemples d'utilisation

### Créer une transaction

```lean
import IrisAxioms.iris_axioms

open IrisAxioms

def exemple_transaction : Transaction := {
  emetteur := TU.mk "Alice"
  recepteur := TU.mk "Bob"
  montant_V := 100.0
  montant_U := 50.0
  preuve_signature := Hash.mk "signature_cryptographique"
  horodatage := 1234567890
  h_montant_V := by norm_num
  h_montant_U := by norm_num
}
```

### Vérifier la conservation monétaire

```lean
-- Voir IrisAxioms/iris_exemples_numeriques.lean
theorem conservation_exemple : ∃ v : Valeurs, v.S + v.U + v.V + v.D = 0 := by
  use { S := 1000, U := 500, V := -1200, D := -300,
        hS := by norm_num, hU := by norm_num,
        hV := by norm_num, hD := by norm_num }
  norm_num
```

## 🔧 Commandes utiles

```bash
# Compiler rapidement (sans Mathlib)
lake build IrisAxioms

# Nettoyer les fichiers compilés
lake clean

# Mettre à jour les dépendances
lake update

# Rechercher des théorèmes
lake env lean --run search_tool.lean

# Formater le code
lake exe format
```

## 🐛 Résolution de problèmes

### Erreur : `lake: command not found`

Assurez-vous que elan est correctement installé et dans votre PATH :
```bash
source ~/.profile
elan toolchain list
```

### Erreur : Compilation très lente

C'est normal pour la première compilation de Mathlib. Pour accélérer :
```bash
# Télécharger les binaires pré-compilés de Mathlib
lake exe cache get
```

### Erreur : `unknown package 'mathlib'`

```bash
lake update
lake clean
lake build
```

### Problème de mémoire

Mathlib nécessite beaucoup de RAM. Si compilation échoue :
- Fermer les autres applications
- Augmenter le swap système
- Compiler module par module au lieu de `lake build`

## 📖 Documentation Lean

- [Manuel Lean 4](https://lean-lang.org/lean4/doc/)
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) (communauté)

## 🤝 Contribution

1. Fork le projet
2. Créer une branche (`git checkout -b feature/amelioration`)
3. Commit vos changements (`git commit -m 'Ajout de nouvelle fonctionnalité'`)
4. Push vers la branche (`git push origin feature/amelioration`)
5. Ouvrir une Pull Request

### Standards de code

- **Preuves complètes** : Pas de `sorry`
- **Documentation** : Commentaires `/-! ... -/` pour les sections
- **Nomenclature** : CamelCase pour les types, snake_case pour les définitions
- **Tests** : Exemples numériques dans `iris_exemples_numeriques.lean`

## 📜 Licence

[À définir selon votre projet]

## 📧 Contact

Pour toute question ou suggestion, ouvrir une issue sur GitHub.

---

**Statut** : ✅ Toutes les preuves sont vérifiées et complètes (sans `sorry`)

**Version Lean** : 4.24.0
**Version Mathlib** : 4.24.0
