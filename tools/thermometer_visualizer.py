#!/usr/bin/env python3
"""
IRIS Economic Thermometer Visualizer

This tool visualizes the IRIS economic thermometer (r_t = D_total / V_on_total)
and simulates its evolution over time with automatic η and κ adjustment.

NOTE: Sign Convention for D (Debt)
    In the Lean formalization: D ≤ 0 (debt is thermodynamically negative by definition).
    This visualizer uses: D > 0 for intuitive display (positive debt values).
    Both conventions represent the same economic reality: D mirrors created value V.

    The simulator applies monthly debt amortization (δ_D ≈ 0.1042% per cycle for ~80 year horizon)
    to model the natural dissipation of the thermometric liability.

Usage:
    python3 thermometer_visualizer.py
    python3 thermometer_visualizer.py --D_total=120000 --V_on_total=100000
    python3 thermometer_visualizer.py --simulate --cycles=100
    python3 thermometer_visualizer.py --simulate --cycles=50 --export_csv=results.csv
    python3 thermometer_visualizer.py --cold_threshold=0.80 --hot_threshold=1.20
    python3 thermometer_visualizer.py --simulate --delta_D_per_cycle=0.001
"""

import matplotlib.pyplot as plt
import numpy as np
import argparse
import csv
from dataclasses import dataclass
from typing import List, Tuple, Optional


@dataclass
class RAD:
    """Registre Automatique de Distribution"""
    D_total: float
    V_on_total: float
    eta: float
    kappa: float

    def thermometre(self) -> float:
        """Calculate r_t = D_total / V_on_total"""
        if self.V_on_total == 0:
            return float('inf')
        return self.D_total / self.V_on_total

    def is_cold(self, cold_threshold: float = 0.85) -> bool:
        """r_t < cold_threshold → System is cold (deflation)"""
        return self.thermometre() < cold_threshold

    def is_hot(self, hot_threshold: float = 1.15) -> bool:
        """r_t > hot_threshold → System is hot (inflation)"""
        return self.thermometre() > hot_threshold

    def is_equilibrium(self, cold_threshold: float = 0.85, hot_threshold: float = 1.15) -> bool:
        """cold_threshold ≤ r_t ≤ hot_threshold → System is in equilibrium"""
        r_t = self.thermometre()
        return cold_threshold <= r_t <= hot_threshold


class IrisThermometerVisualizer:
    """Visualizer for IRIS economic thermometer"""

    def __init__(self, cold_threshold: float = 0.85, hot_threshold: float = 1.15):
        """
        Initialize visualizer with configurable thresholds

        Args:
            cold_threshold: r_t threshold below which system is cold (default: 0.85)
            hot_threshold: r_t threshold above which system is hot (default: 1.15)
        """
        self.cold_threshold = cold_threshold
        self.hot_threshold = hot_threshold
        self.zones = {
            'cold': (0, cold_threshold, 'blue', 'COLD\n(Deflation)'),
            'equilibrium': (cold_threshold, hot_threshold, 'green', 'EQUILIBRIUM'),
            'hot': (hot_threshold, 3.0, 'red', 'HOT\n(Inflation)')
        }

    def get_color(self, r_t: float) -> str:
        """Get color based on thermometer value"""
        for zone, (min_val, max_val, color, _) in self.zones.items():
            if min_val <= r_t <= max_val:
                return color
        return 'gray'

    def get_zone_name(self, r_t: float) -> str:
        """Get zone name based on thermometer value"""
        for zone, (min_val, max_val, _, name) in self.zones.items():
            if min_val <= r_t <= max_val:
                return name
        return 'UNKNOWN'

    def plot_current_state(self, rad: RAD, save_path: str = 'thermometer_state.png'):
        """Plot current thermometer state"""
        r_t = rad.thermometre()

        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

        # Graph 1: Current thermometer reading
        ax1.barh(['Thermometer'], [min(r_t, 3.0)], color=self.get_color(r_t), alpha=0.7)
        ax1.axvline(x=self.cold_threshold, color='blue', linestyle='--', linewidth=2, alpha=0.7,
                   label=f'Cold threshold ({self.cold_threshold})')
        ax1.axvline(x=self.hot_threshold, color='red', linestyle='--', linewidth=2, alpha=0.7,
                   label=f'Hot threshold ({self.hot_threshold})')
        ax1.axvspan(self.cold_threshold, self.hot_threshold, alpha=0.2, color='green', label='Equilibrium zone')
        ax1.set_xlim(0, 3)
        ax1.set_xlabel('r_t = D_total / V_on_total', fontsize=12)
        ax1.set_title(f'Economic State: r_t = {r_t:.2f}\nZone: {self.get_zone_name(r_t)}',
                     fontsize=14, fontweight='bold')
        ax1.legend(loc='upper right')
        ax1.grid(True, alpha=0.3)

        # Graph 2: System parameters
        params = ['D_total', 'V_on_total', 'η', 'κ']
        values = [rad.D_total, rad.V_on_total, rad.eta, rad.kappa]
        colors = ['orangered', 'lightblue', 'purple', 'orange']

        ax2.barh(params, values, color=colors, alpha=0.7)
        ax2.set_xlabel('Value', fontsize=12)
        ax2.set_title('RAD Parameters', fontsize=14, fontweight='bold')
        ax2.grid(True, alpha=0.3, axis='x')

        # Add value labels
        for i, v in enumerate(values):
            ax2.text(v + max(values) * 0.02, i, f'{v:.2f}',
                    va='center', fontsize=10, fontweight='bold')

        plt.tight_layout()
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Plot saved to {save_path}")
        plt.show()

    def simulate_evolution(self, rad_initial: RAD, cycles: int = 100,
                          adjustment_rate: float = 0.1,
                          delta_D_per_cycle: float = 0.001041666) -> List[Tuple[int, RAD]]:
        """
        Simulate economic evolution with automatic η and κ adjustment + debt amortization

        Args:
            rad_initial: Initial RAD state
            cycles: Number of cycles to simulate
            adjustment_rate: Rate of η and κ adjustment (default 10%)
            delta_D_per_cycle: Monthly debt amortization rate (default 0.001041666 ≈ 0.1042%)

        Returns:
            List of (cycle, RAD) tuples

        Notes:
            - Applies debt amortization FIRST: D ← D × (1 - δ_D)
            - Then adjusts η and κ based on thermometer zones
            - Enforces bounds: 0.5 ≤ η, κ ≤ 2.0
            - Enforces variation limits: |Δη|, |Δκ| ≤ 0.15 per cycle
        """
        history = [(0, rad_initial)]
        rad_current = rad_initial

        for cycle in range(1, cycles + 1):
            # 1. Apply debt amortization FIRST
            current_D = rad_current.D_total * (1 - delta_D_per_cycle)

            # 2. Calculate thermometer
            r_t = current_D / rad_current.V_on_total

            # 3. Apply A20 automatic adjustment for both η and κ
            delta_eta = 0.0
            delta_kappa = 0.0

            if r_t > self.hot_threshold:  # Hot → reduce η and κ
                delta_eta = -rad_current.eta * adjustment_rate
                delta_kappa = -rad_current.kappa * adjustment_rate
            elif r_t < self.cold_threshold:  # Cold → increase η and κ
                delta_eta = rad_current.eta * adjustment_rate
                delta_kappa = rad_current.kappa * adjustment_rate
            # Equilibrium → no change

            # 4. Apply variation limits: |Δη|, |Δκ| ≤ 0.15
            delta_eta = max(-0.15, min(0.15, delta_eta))
            delta_kappa = max(-0.15, min(0.15, delta_kappa))

            new_eta = rad_current.eta + delta_eta
            new_kappa = rad_current.kappa + delta_kappa

            # 5. Apply bounds: 0.5 ≤ η, κ ≤ 2.0
            new_eta = max(0.5, min(2.0, new_eta))
            new_kappa = max(0.5, min(2.0, new_kappa))

            # 6. Simulate value creation: ΔV = η × E (simplified)
            # Assume constant energy input E = 1000 per cycle
            E_per_cycle = 1000
            delta_V = new_eta * E_per_cycle
            delta_D_creation = -delta_V  # Conservation: D mirrors V

            # Update RAD state
            rad_next = RAD(
                D_total=current_D + delta_D_creation,
                V_on_total=rad_current.V_on_total + delta_V,
                eta=new_eta,
                kappa=new_kappa
            )

            history.append((cycle, rad_next))
            rad_current = rad_next

        return history

    def plot_evolution(self, history: List[Tuple[int, RAD]],
                      save_path: str = 'thermometer_evolution.png'):
        """Plot thermometer evolution over time"""
        cycles = [h[0] for h in history]
        r_t_values = [h[1].thermometre() for h in history]
        eta_values = [h[1].eta for h in history]
        kappa_values = [h[1].kappa for h in history]
        V_values = [h[1].V_on_total for h in history]
        D_values = [h[1].D_total for h in history]

        fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))

        # Plot 1: Thermometer evolution
        ax1.plot(cycles, r_t_values, 'b-', linewidth=2, label='r_t')
        ax1.axhline(y=self.cold_threshold, color='blue', linestyle='--', alpha=0.5,
                   label=f'Cold threshold ({self.cold_threshold})')
        ax1.axhline(y=self.hot_threshold, color='red', linestyle='--', alpha=0.5,
                   label=f'Hot threshold ({self.hot_threshold})')
        ax1.fill_between(cycles, self.cold_threshold, self.hot_threshold, alpha=0.2, color='green',
                        label='Equilibrium zone')
        ax1.set_xlabel('Cycle', fontsize=12)
        ax1.set_ylabel('r_t = D_total / V_on_total', fontsize=12)
        ax1.set_title('Economic Thermometer Evolution', fontsize=14, fontweight='bold')
        ax1.legend()
        ax1.grid(True, alpha=0.3)

        # Plot 2: η and κ evolution
        ax2.plot(cycles, eta_values, 'purple', linewidth=2, label='η (Value creation)')
        ax2.plot(cycles, kappa_values, 'orange', linewidth=2, label='κ (U→V conversion)')
        ax2.axhline(y=0.5, color='gray', linestyle=':', alpha=0.5, label='Lower bound (0.5)')
        ax2.axhline(y=2.0, color='gray', linestyle=':', alpha=0.5, label='Upper bound (2.0)')
        ax2.set_xlabel('Cycle', fontsize=12)
        ax2.set_ylabel('Coefficients', fontsize=12)
        ax2.set_title('η and κ Automatic Adjustment', fontsize=14, fontweight='bold')
        ax2.set_ylim(0.4, 2.1)
        ax2.legend()
        ax2.grid(True, alpha=0.3)

        # Plot 3: V_on_total evolution
        ax3.plot(cycles, V_values, 'lightblue', linewidth=2, label='V_on_total')
        ax3.set_xlabel('Cycle', fontsize=12)
        ax3.set_ylabel('V_on_total', fontsize=12)
        ax3.set_title('Circulating Value Evolution', fontsize=14, fontweight='bold')
        ax3.legend()
        ax3.grid(True, alpha=0.3)
        ax3.ticklabel_format(style='plain', axis='y')

        # Plot 4: D_total evolution
        ax4.plot(cycles, D_values, 'orangered', linewidth=2, label='D_total')
        ax4.set_xlabel('Cycle', fontsize=12)
        ax4.set_ylabel('D_total', fontsize=12)
        ax4.set_title('Total Debt Evolution (with amortization)', fontsize=14, fontweight='bold')
        ax4.legend()
        ax4.grid(True, alpha=0.3)
        ax4.ticklabel_format(style='plain', axis='y')

        plt.tight_layout()
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Evolution plot saved to {save_path}")
        plt.show()

    def print_summary(self, history: List[Tuple[int, RAD]], delta_D_per_cycle: float = 0.001041666):
        """Print summary statistics"""
        print("\n" + "=" * 60)
        print("IRIS ECONOMIC SIMULATION SUMMARY")
        print("=" * 60)

        initial = history[0][1]
        final = history[-1][1]

        print(f"\nInitial State (Cycle 0):")
        print(f"  r_t = {initial.thermometre():.2f}")
        print(f"  D_total = {initial.D_total:.2f}")
        print(f"  V_on_total = {initial.V_on_total:.2f}")
        print(f"  η = {initial.eta:.2f}")
        print(f"  κ = {initial.kappa:.2f}")
        print(f"  Zone: {self.get_zone_name(initial.thermometre())}")

        print(f"\nFinal State (Cycle {history[-1][0]}):")
        print(f"  r_t = {final.thermometre():.2f}")
        print(f"  D_total = {final.D_total:.2f}")
        print(f"  V_on_total = {final.V_on_total:.2f}")
        print(f"  η = {final.eta:.2f}")
        print(f"  κ = {final.kappa:.2f}")
        print(f"  Zone: {self.get_zone_name(final.thermometre())}")

        # Statistics
        r_t_values = [h[1].thermometre() for h in history]
        equilibrium_cycles = sum(1 for r_t in r_t_values
                                if self.cold_threshold <= r_t <= self.hot_threshold)

        print(f"\nSimulation Parameters:")
        print(f"  δ_D (debt amortization): {delta_D_per_cycle * 100:.4f}% per cycle")
        print(f"  Thresholds: cold={self.cold_threshold}, hot={self.hot_threshold}")
        print(f"  Bounds: 0.5 ≤ η, κ ≤ 2.0")
        print(f"  Max variation: |Δη|, |Δκ| ≤ 0.15 per cycle")

        print(f"\nStatistics:")
        print(f"  Total cycles: {len(history) - 1}")
        print(f"  Cycles in equilibrium: {equilibrium_cycles} ({equilibrium_cycles / len(history) * 100:.1f}%)")
        print(f"  Average r_t: {np.mean(r_t_values):.2f}")
        print(f"  r_t std dev: {np.std(r_t_values):.2f}")
        print(f"  Final η change: {(final.eta - initial.eta) / initial.eta * 100:+.1f}%")
        print(f"  Final κ change: {(final.kappa - initial.kappa) / initial.kappa * 100:+.1f}%")
        print(f"  Final V growth: {(final.V_on_total - initial.V_on_total) / initial.V_on_total * 100:+.1f}%")
        print(f"  Final D change: {(final.D_total - initial.D_total) / initial.D_total * 100:+.1f}%")

        print("\n" + "=" * 60 + "\n")

    def export_to_csv(self, history: List[Tuple[int, RAD]], filename: str,
                     delta_D_per_cycle: float = 0.001041666):
        """
        Export simulation history to CSV file

        Args:
            history: List of (cycle, RAD) tuples from simulate_evolution
            filename: Output CSV filename
            delta_D_per_cycle: Debt amortization rate used in simulation
        """
        with open(filename, 'w', newline='') as csvfile:
            fieldnames = ['cycle', 'r_t', 'D_total', 'V_on_total', 'eta', 'kappa',
                         'delta_D_per_cycle', 'zone']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

            writer.writeheader()
            for cycle, rad in history:
                r_t = rad.thermometre()
                writer.writerow({
                    'cycle': cycle,
                    'r_t': round(r_t, 4),
                    'D_total': round(rad.D_total, 2),
                    'V_on_total': round(rad.V_on_total, 2),
                    'eta': round(rad.eta, 4),
                    'kappa': round(rad.kappa, 4),
                    'delta_D_per_cycle': round(delta_D_per_cycle, 6),
                    'zone': self.get_zone_name(r_t).replace('\n', ' ')
                })

        print(f"✓ CSV data exported to {filename}")


def main():
    parser = argparse.ArgumentParser(description='IRIS Economic Thermometer Visualizer')
    parser.add_argument('--D_total', type=float, default=120000,
                       help='Total debt (default: 120000)')
    parser.add_argument('--V_on_total', type=float, default=100000,
                       help='Total circulating value (default: 100000)')
    parser.add_argument('--eta', type=float, default=1.2,
                       help='Value creation efficiency (default: 1.2)')
    parser.add_argument('--kappa', type=float, default=0.8,
                       help='Conversion coefficient U→V (default: 0.8)')
    parser.add_argument('--simulate', action='store_true',
                       help='Run time evolution simulation')
    parser.add_argument('--cycles', type=int, default=100,
                       help='Number of cycles for simulation (default: 100)')
    parser.add_argument('--adjustment_rate', type=float, default=0.1,
                       help='η and κ adjustment rate (default: 0.1 = 10%%)')
    parser.add_argument('--delta_D_per_cycle', type=float, default=0.001041666,
                       help='Debt amortization rate per cycle (default: 0.001041666 ≈ 0.1042%%)')
    parser.add_argument('--cold_threshold', type=float, default=0.85,
                       help='Cold zone threshold (default: 0.85)')
    parser.add_argument('--hot_threshold', type=float, default=1.15,
                       help='Hot zone threshold (default: 1.15)')
    parser.add_argument('--export_csv', type=str, default=None,
                       help='Export simulation results to CSV file (requires --simulate)')

    args = parser.parse_args()

    # Create initial RAD
    rad = RAD(
        D_total=args.D_total,
        V_on_total=args.V_on_total,
        eta=args.eta,
        kappa=args.kappa
    )

    # Create visualizer with configurable thresholds
    viz = IrisThermometerVisualizer(
        cold_threshold=args.cold_threshold,
        hot_threshold=args.hot_threshold
    )

    if args.simulate:
        # Run simulation
        print(f"Running simulation for {args.cycles} cycles...")
        print(f"Using thresholds: cold={args.cold_threshold}, hot={args.hot_threshold}")
        print(f"Debt amortization: δ_D = {args.delta_D_per_cycle * 100:.4f}% per cycle")
        print(f"Adjustment rate: {args.adjustment_rate * 100:.1f}%")
        print(f"Bounds: 0.5 ≤ η, κ ≤ 2.0 | Max variation: |Δη|, |Δκ| ≤ 0.15")

        history = viz.simulate_evolution(
            rad,
            cycles=args.cycles,
            adjustment_rate=args.adjustment_rate,
            delta_D_per_cycle=args.delta_D_per_cycle
        )
        viz.plot_evolution(history)
        viz.print_summary(history, delta_D_per_cycle=args.delta_D_per_cycle)

        # Export to CSV if requested
        if args.export_csv:
            viz.export_to_csv(history, args.export_csv, delta_D_per_cycle=args.delta_D_per_cycle)
    else:
        # Show current state
        viz.plot_current_state(rad)

        # Print state info
        print(f"\nCurrent Economic State:")
        print(f"  r_t = {rad.thermometre():.2f}")
        print(f"  Zone: {viz.get_zone_name(rad.thermometre())}")
        print(f"  Status: ", end='')
        if rad.is_cold(args.cold_threshold):
            print("COLD - System needs more value creation (increase η and κ)")
        elif rad.is_hot(args.hot_threshold):
            print("HOT - System has too much debt (decrease η and κ)")
        else:
            print("EQUILIBRIUM - System is balanced")


if __name__ == '__main__':
    main()
