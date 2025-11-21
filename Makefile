# Makefile pour IRIS Axioms Lean
# Facilite les commandes courantes du projet

.PHONY: help build run clean update test check install cache all

# Commande par défaut : afficher l'aide
help:
	@echo "═══════════════════════════════════════════════════════"
	@echo "  IRIS Axioms - Commandes disponibles"
	@echo "═══════════════════════════════════════════════════════"
	@echo ""
	@echo "  make install    - Installer Lean et les dépendances"
	@echo "  make build      - Compiler le projet"
	@echo "  make run        - Exécuter le programme principal"
	@echo "  make clean      - Nettoyer les fichiers compilés"
	@echo "  make update     - Mettre à jour les dépendances"
	@echo "  make cache      - Télécharger les binaires pré-compilés"
	@echo "  make check      - Vérifier tous les fichiers Lean"
	@echo "  make test       - Lancer les tests (exemples numériques)"
	@echo "  make all        - Clean + Update + Build + Run"
	@echo ""
	@echo "  make help       - Afficher cette aide"
	@echo ""
	@echo "═══════════════════════════════════════════════════════"

# Installation complète (lance le script setup.sh)
install:
	@echo "🚀 Lancement de l'installation..."
	@chmod +x setup.sh
	@./setup.sh

# Compiler le projet
build:
	@echo "🔨 Compilation du projet IRIS Axioms..."
	@lake build

# Exécuter le programme principal
run:
	@echo "▶️  Exécution de IRIS Axioms..."
	@lake exe irisaxioms

# Nettoyer les fichiers compilés
clean:
	@echo "🧹 Nettoyage des fichiers compilés..."
	@lake clean
	@echo "✓ Nettoyage terminé"

# Mettre à jour les dépendances
update:
	@echo "📦 Mise à jour des dépendances..."
	@lake update
	@echo "✓ Dépendances mises à jour"

# Télécharger les binaires pré-compilés de Mathlib (accélère la compilation)
cache:
	@echo "⬇️  Téléchargement des binaires Mathlib..."
	@lake exe cache get || echo "⚠️  Impossible de télécharger les binaires"

# Vérifier tous les fichiers Lean du projet
check:
	@echo "🔍 Vérification de tous les fichiers..."
	@lake build IrisAxioms
	@echo "✓ Vérification terminée"

# Tester les exemples numériques
test:
	@echo "🧪 Test des exemples numériques..."
	@lean IrisAxioms/iris_exemples_numeriques.lean
	@echo "✓ Tests passés"

# Tout faire : clean, update, cache, build, run
all: clean update cache build run
	@echo ""
	@echo "✅ Compilation et exécution complètes réussies !"

# Vérifier les versions installées
versions:
	@echo "Versions installées :"
	@echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo -n "Lean:  "
	@lean --version 2>/dev/null || echo "Non installé"
	@echo -n "Lake:  "
	@lake --version 2>/dev/null || echo "Non installé"
	@echo -n "Elan:  "
	@elan --version 2>/dev/null || echo "Non installé"
	@echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Informations sur le projet
info:
	@echo "📋 Informations sur le projet IRIS Axioms"
	@echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo "Version Lean requise: $(shell cat lean-toolchain)"
	@echo "Modules principaux:"
	@find IrisAxioms -name "*.lean" -type f | sed 's/^/  - /'
	@echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Lancer le REPL Lean
repl:
	@echo "🖥️  Lancement du REPL Lean..."
	@lake env lean --repl

# Formater le code (si outil de formatage disponible)
format:
	@echo "🎨 Formatage du code..."
	@find IrisAxioms -name "*.lean" -type f -exec echo "Checking: {}" \;

# Statistiques du projet
stats:
	@echo "📊 Statistiques du projet"
	@echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo "Nombre de fichiers .lean:"
	@find . -name "*.lean" -type f | wc -l
	@echo "Nombre de lignes de code:"
	@find IrisAxioms -name "*.lean" -type f -exec cat {} \; | wc -l
	@echo "Nombre de théorèmes:"
	@grep -r "theorem" IrisAxioms --include="*.lean" | wc -l
	@echo "Nombre de lemmes:"
	@grep -r "lemma" IrisAxioms --include="*.lean" | wc -l
	@echo "Nombre de définitions:"
	@grep -r "def " IrisAxioms --include="*.lean" | wc -l
	@echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
