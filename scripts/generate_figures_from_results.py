#!/usr/bin/env python3
"""
Generate figures from real computation results for the paper.

This script creates professional figures showing:
1. Correlation coefficient distribution
2. Cancellation constant vs correlation
3. Error sequences visualization
4. Comparison across primes
"""

import json
import numpy as np
import matplotlib.pyplot as plt
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend

# Set style for publication quality
plt.style.use('seaborn-v0_8-paper')
matplotlib.rcParams['font.family'] = 'serif'
matplotlib.rcParams['font.serif'] = ['Times New Roman', 'Computer Modern Roman']
matplotlib.rcParams['font.size'] = 11
matplotlib.rcParams['axes.labelsize'] = 12
matplotlib.rcParams['axes.titlesize'] = 13
matplotlib.rcParams['xtick.labelsize'] = 10
matplotlib.rcParams['ytick.labelsize'] = 10
matplotlib.rcParams['legend.fontsize'] = 10
matplotlib.rcParams['figure.dpi'] = 300

def load_results():
    """Load computation results."""
    with open('scripts/computation_results.json', 'r') as f:
        return json.load(f)

def figure_correlation_distribution(results):
    """Figure 1: Distribution of correlation coefficients."""
    rhos = [r['rho'] for r in results]
    
    fig, ax = plt.subplots(figsize=(8, 6))
    
    ax.hist(rhos, bins=30, edgecolor='black', alpha=0.7, color='steelblue')
    ax.axvline(np.mean(rhos), color='red', linestyle='--', linewidth=2, 
               label=f'Mean: {np.mean(rhos):.4f}')
    ax.axvline(0, color='green', linestyle=':', linewidth=1.5, 
               label='Zero correlation')
    
    ax.set_xlabel('Correlation Coefficient $\\rho$', fontsize=12)
    ax.set_ylabel('Frequency', fontsize=12)
    ax.set_title('Distribution of Correlation Coefficients from Real IUT Construction', 
                 fontsize=13, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('scripts/fig_correlation_distribution.pdf', bbox_inches='tight', dpi=300)
    plt.savefig('scripts/fig_correlation_distribution.png', bbox_inches='tight', dpi=300)
    print("Generated: fig_correlation_distribution.pdf")

def figure_cancellation_vs_correlation(results):
    """Figure 2: Cancellation constant vs correlation."""
    rhos = [r['rho'] for r in results]
    Ks = [r['K'] for r in results]
    
    # Theoretical curve
    rho_theory = np.linspace(-0.5, 0.5, 1000)
    K_theory = 4.0 / (1.0 + rho_theory)**2
    
    fig, ax = plt.subplots(figsize=(8, 6))
    
    # Theoretical curve
    ax.plot(rho_theory, K_theory, 'b-', linewidth=2, label='Theoretical: $K = 4/(1+\\rho)^2$')
    
    # Actual data points
    ax.scatter(rhos, Ks, color='red', s=50, alpha=0.6, zorder=5, 
               label='Computed values')
    
    # Highlight rho = 0
    ax.axvline(0, color='green', linestyle=':', linewidth=1.5, alpha=0.5)
    ax.axhline(4, color='green', linestyle=':', linewidth=1.5, alpha=0.5)
    ax.plot(0, 4, 'go', markersize=10, label='Uncorrelated: $\\rho=0, K=4$')
    
    ax.set_xlabel('Correlation Coefficient $\\rho$', fontsize=12)
    ax.set_ylabel('Cancellation Constant $K$', fontsize=12)
    ax.set_title('Cancellation Constant vs Correlation Coefficient', 
                 fontsize=13, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_xlim(-0.5, 0.5)
    ax.set_ylim(0, 8)
    
    plt.tight_layout()
    plt.savefig('scripts/fig_cancellation_vs_correlation.pdf', bbox_inches='tight', dpi=300)
    plt.savefig('scripts/fig_cancellation_vs_correlation.png', bbox_inches='tight', dpi=300)
    print("Generated: fig_cancellation_vs_correlation.pdf")

def figure_error_sequences(results):
    """Figure 3: Error sequences for main example."""
    # Find main example (E: y² = x³ + x + 1, p = 13)
    main_result = None
    for r in results:
        if r['curve']['a'] == 0 and r['curve']['b'] == 1 and r['curve']['c'] == 1 and r['prime'] == 13:
            main_result = r
            break
    
    if not main_result:
        print("Main example not found, using first result")
        main_result = results[0]
    
    errors_11 = main_result['errors_11']
    errors_22 = main_result['errors_22']
    steps = range(1, len(errors_11) + 1)
    
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8))
    
    # Error sequence 11
    ax1.plot(steps, errors_11, 'o-', color='blue', linewidth=2, markersize=6, 
             label='$\\epsilon_{11}$ (Frobenius component)')
    ax1.set_xlabel('Step $j$', fontsize=12)
    ax1.set_ylabel('Error $\\epsilon_{11}$', fontsize=12)
    ax1.set_title('Diagonal Error Sequence: Frobenius Component', fontsize=12, fontweight='bold')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Error sequence 22
    ax2.plot(steps, errors_22, 's-', color='red', linewidth=2, markersize=6,
             label='$\\epsilon_{22}$ (Multiplicative component)')
    ax2.set_xlabel('Step $j$', fontsize=12)
    ax2.set_ylabel('Error $\\epsilon_{22}$', fontsize=12)
    ax2.set_title('Diagonal Error Sequence: Multiplicative Component', fontsize=12, fontweight='bold')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('scripts/fig_error_sequences.pdf', bbox_inches='tight', dpi=300)
    plt.savefig('scripts/fig_error_sequences.png', bbox_inches='tight', dpi=300)
    print("Generated: fig_error_sequences.pdf")

def figure_rho_across_primes(results):
    """Figure 4: Correlation coefficient across primes."""
    # Group by curve
    curves = {}
    for r in results:
        curve_key = f"y² = x³ + {r['curve']['a']}x² + {r['curve']['b']}x + {r['curve']['c']}"
        if curve_key not in curves:
            curves[curve_key] = []
        curves[curve_key].append((r['prime'], r['rho']))
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    colors = ['blue', 'red', 'green', 'orange', 'purple', 'brown']
    markers = ['o', 's', '^', 'v', 'D', 'p']
    
    for idx, (curve_name, data) in enumerate(curves.items()):
        data.sort(key=lambda x: x[0])  # Sort by prime
        primes = [d[0] for d in data]
        rhos = [d[1] for d in data]
        
        ax.plot(primes, rhos, marker=markers[idx % len(markers)], 
                linewidth=2, markersize=8, label=curve_name[:25],
                color=colors[idx % len(colors)])
    
    ax.axhline(0, color='black', linestyle='--', linewidth=1, alpha=0.5)
    ax.set_xlabel('Prime $p$', fontsize=12)
    ax.set_ylabel('Correlation Coefficient $\\rho$', fontsize=12)
    ax.set_title('Correlation Coefficient Across Primes (Real IUT Construction)', 
                 fontsize=13, fontweight='bold')
    ax.legend(loc='best', fontsize=9)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('scripts/fig_rho_across_primes.pdf', bbox_inches='tight', dpi=300)
    plt.savefig('scripts/fig_rho_across_primes.png', bbox_inches='tight', dpi=300)
    print("Generated: fig_rho_across_primes.pdf")

def figure_scatter_errors(results):
    """Figure 5: Scatter plot of errors showing correlation."""
    # Use main example
    main_result = None
    for r in results:
        if r['curve']['a'] == 0 and r['curve']['b'] == 1 and r['curve']['c'] == 1 and r['prime'] == 13:
            main_result = r
            break
    
    if not main_result:
        main_result = results[0]
    
    errors_11 = main_result['errors_11']
    errors_22 = main_result['errors_22']
    rho = main_result['rho']
    
    fig, ax = plt.subplots(figsize=(8, 8))
    
    ax.scatter(errors_11, errors_22, s=100, alpha=0.6, color='steelblue', edgecolors='black', linewidth=1)
    
    # Add correlation line
    mean_11 = np.mean(errors_11)
    mean_22 = np.mean(errors_22)
    std_11 = np.std(errors_11)
    std_22 = np.std(errors_22)
    
    if std_11 > 0:
        x_line = np.linspace(min(errors_11), max(errors_11), 100)
        y_line = mean_22 + rho * (std_22 / std_11) * (x_line - mean_11)
        ax.plot(x_line, y_line, 'r--', linewidth=2, 
                label=f'Correlation line ($\\rho = {rho:.4f}$)')
    
    ax.axhline(mean_22, color='gray', linestyle=':', linewidth=1, alpha=0.5)
    ax.axvline(mean_11, color='gray', linestyle=':', linewidth=1, alpha=0.5)
    
    ax.set_xlabel('Error $\\epsilon_{11}$ (Frobenius component)', fontsize=12)
    ax.set_ylabel('Error $\\epsilon_{22}$ (Multiplicative component)', fontsize=12)
    ax.set_title(f'Error Correlation Scatter Plot ($\\rho = {rho:.4f}$)', 
                 fontsize=13, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('scripts/fig_scatter_errors.pdf', bbox_inches='tight', dpi=300)
    plt.savefig('scripts/fig_scatter_errors.png', bbox_inches='tight', dpi=300)
    print("Generated: fig_scatter_errors.pdf")

def main():
    """Generate all figures."""
    print("="*70)
    print("GENERATING FIGURES FROM REAL COMPUTATION RESULTS")
    print("="*70)
    
    results = load_results()
    print(f"Loaded {len(results)} computation results")
    
    figure_correlation_distribution(results)
    figure_cancellation_vs_correlation(results)
    figure_error_sequences(results)
    figure_rho_across_primes(results)
    figure_scatter_errors(results)
    
    print("\n" + "="*70)
    print("ALL FIGURES GENERATED")
    print("="*70)

if __name__ == "__main__":
    main()
