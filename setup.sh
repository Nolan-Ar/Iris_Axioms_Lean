#!/bin/bash

# Script d'installation pour IRIS Axioms Lean
# Automatise l'installation de Lean 4 et la compilation du projet

set -e  # Arrêter en cas d'erreur

# Couleurs pour l'affichage
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}╔════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  IRIS Axioms - Installation Setup     ║${NC}"
echo -e "${BLUE}╔════════════════════════════════════════╗${NC}"
echo ""

# Fonction pour afficher les étapes
step() {
    echo -e "${BLUE}[ÉTAPE]${NC} $1"
}

success() {
    echo -e "${GREEN}[✓]${NC} $1"
}

warning() {
    echo -e "${YELLOW}[!]${NC} $1"
}

error() {
    echo -e "${RED}[✗]${NC} $1"
}

# Vérifier si Lean est déjà installé
step "Vérification de Lean 4..."
if command -v lean &> /dev/null; then
    LEAN_VERSION=$(lean --version | head -n 1)
    success "Lean est déjà installé : $LEAN_VERSION"

    # Vérifier la version
    if lean --version | grep -q "4.24.0"; then
        success "Version correcte détectée (4.24.0)"
    else
        warning "Version différente de 4.24.0 détectée"
        echo "   Le projet utilise Lean 4.24.0 (spécifié dans lean-toolchain)"
        echo "   Elan va automatiquement utiliser la bonne version."
    fi
else
    warning "Lean n'est pas installé"

    # Vérifier si elan est installé
    if command -v elan &> /dev/null; then
        success "Elan (gestionnaire Lean) est déjà installé"
    else
        step "Installation de elan (gestionnaire de versions Lean)..."

        # Vérifier si curl est disponible
        if ! command -v curl &> /dev/null; then
            error "curl n'est pas installé. Veuillez l'installer :"
            echo "  - Ubuntu/Debian: sudo apt install curl"
            echo "  - macOS: brew install curl"
            echo "  - Fedora: sudo dnf install curl"
            exit 1
        fi

        # Installer elan
        echo "Téléchargement et installation de elan..."
        curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

        # Configurer le PATH pour la session actuelle
        export PATH="$HOME/.elan/bin:$PATH"

        success "Elan installé avec succès"
        warning "IMPORTANT: Redémarrez votre terminal ou exécutez:"
        echo "    source ~/.profile    # ou ~/.bashrc selon votre shell"
    fi
fi

# Vérifier si lake est disponible
step "Vérification de Lake (outil de build Lean)..."
if command -v lake &> /dev/null; then
    success "Lake est disponible"
else
    error "Lake n'est pas dans le PATH"
    echo "Veuillez exécuter : source ~/.profile"
    exit 1
fi

# Mise à jour des dépendances
step "Récupération des dépendances du projet..."
echo "Cela peut prendre quelques minutes..."
if lake update; then
    success "Dépendances mises à jour"
else
    warning "Erreur lors de la mise à jour des dépendances"
    echo "Tentative de récupération..."
fi

# Tentative de téléchargement des binaires pré-compilés de Mathlib
step "Tentative de téléchargement des binaires Mathlib..."
echo "Cela accélère considérablement la compilation..."
if lake exe cache get 2>/dev/null; then
    success "Binaires Mathlib téléchargés"
else
    warning "Impossible de télécharger les binaires pré-compilés"
    echo "   La compilation complète de Mathlib sera nécessaire (20-40 min)"
fi

# Compilation du projet
step "Compilation du projet IRIS Axioms..."
echo "Première compilation : cela peut prendre 20-40 minutes..."
echo "Les compilations suivantes seront beaucoup plus rapides."
echo ""

START_TIME=$(date +%s)

if lake build; then
    END_TIME=$(date +%s)
    DURATION=$((END_TIME - START_TIME))
    MINUTES=$((DURATION / 60))
    SECONDS=$((DURATION % 60))

    success "Compilation réussie en ${MINUTES}m ${SECONDS}s"
else
    error "Échec de la compilation"
    echo ""
    echo "Solutions possibles :"
    echo "  1. Vérifier que vous avez au moins 4 GB de RAM disponible"
    echo "  2. Fermer les autres applications"
    echo "  3. Réessayer : lake clean && lake build"
    echo "  4. Compiler module par module au lieu de tout le projet"
    exit 1
fi

# Test de l'exécutable
step "Test de l'exécutable..."
if lake exe irisaxioms; then
    success "L'exécutable fonctionne correctement"
else
    warning "Problème avec l'exécutable"
fi

# Résumé final
echo ""
echo -e "${GREEN}╔════════════════════════════════════════╗${NC}"
echo -e "${GREEN}║     Installation terminée avec succès ! ║${NC}"
echo -e "${GREEN}╚════════════════════════════════════════╝${NC}"
echo ""
echo "Commandes disponibles :"
echo "  lake build              - Compiler le projet"
echo "  lake exe irisaxioms     - Exécuter le programme"
echo "  lake clean              - Nettoyer les fichiers compilés"
echo "  lean <fichier.lean>     - Vérifier un fichier spécifique"
echo ""
echo "Ou utilisez le Makefile :"
echo "  make build              - Compiler"
echo "  make run                - Exécuter"
echo "  make clean              - Nettoyer"
echo ""
echo "Pour travailler confortablement :"
echo "  1. Installez VS Code : https://code.visualstudio.com/"
echo "  2. Installez l'extension Lean 4 (ID: leanprover.lean4)"
echo "  3. Ouvrez ce dossier dans VS Code"
echo ""
success "Prêt à utiliser IRIS Axioms !"
