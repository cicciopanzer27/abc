"""
Analyze extended benchmark results and compare with original 21 computations
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import numpy as np

def load_results(filename):
    """Load computation results from JSON file"""
    with open(filename, 'r') as f:
        return json.load(f)

def analyze_statistics(results):
    """Analyze statistical properties"""
    rhos = [r["rho"] for r in results]
    Ks = [r["K"] for r in results]
    
    print("=" * 80)
    print("STATISTICAL ANALYSIS")
    print("=" * 80)
    print(f"\nTotal computations: {len(results)}")
    
    print(f"\nCorrelation (rho):")
    print(f"  Mean:   {np.mean(rhos):.6f}")
    print(f"  Std:    {np.std(rhos):.6f}")
    print(f"  Min:    {np.min(rhos):.6f}")
    print(f"  Max:    {np.max(rhos):.6f}")
    print(f"  Median: {np.median(rhos):.6f}")
    print(f"  25th percentile: {np.percentile(rhos, 25):.6f}")
    print(f"  75th percentile: {np.percentile(rhos, 75):.6f}")
    
    print(f"\nCancellation Constant (K):")
    print(f"  Mean:   {np.mean(Ks):.6f}")
    print(f"  Std:    {np.std(Ks):.6f}")
    print(f"  Min:    {np.min(Ks):.6f}")
    print(f"  Max:    {np.max(Ks):.6f}")
    print(f"  Median: {np.median(Ks):.6f}")
    print(f"  25th percentile: {np.percentile(Ks, 25):.6f}")
    print(f"  75th percentile: {np.percentile(Ks, 75):.6f}")
    
    # Distribution analysis
    print(f"\nDistribution Analysis:")
    high_corr = sum(1 for r in rhos if r > 0.8)
    medium_corr = sum(1 for r in rhos if 0.3 <= r <= 0.8)
    low_corr = sum(1 for r in rhos if 0 <= r < 0.3)
    zero_corr = sum(1 for r in rhos if abs(r) < 0.01)
    
    print(f"  High correlation (rho > 0.8): {high_corr}/{len(results)} ({100*high_corr/len(results):.1f}%)")
    print(f"  Medium correlation (0.3 <= rho <= 0.8): {medium_corr}/{len(results)} ({100*medium_corr/len(results):.1f}%)")
    print(f"  Low correlation (0 <= rho < 0.3): {low_corr}/{len(results)} ({100*low_corr/len(results):.1f}%)")
    print(f"  Near-zero correlation (|rho| < 0.01): {zero_corr}/{len(results)} ({100*zero_corr/len(results):.1f}%)")
    
    return {
        "n": len(results),
        "rho_mean": float(np.mean(rhos)),
        "rho_std": float(np.std(rhos)),
        "rho_min": float(np.min(rhos)),
        "rho_max": float(np.max(rhos)),
        "rho_median": float(np.median(rhos)),
        "K_mean": float(np.mean(Ks)),
        "K_std": float(np.std(Ks)),
        "K_min": float(np.min(Ks)),
        "K_max": float(np.max(Ks)),
        "K_median": float(np.median(Ks)),
        "high_corr_pct": 100*high_corr/len(results),
        "zero_corr_pct": 100*zero_corr/len(results)
    }

def compare_with_original(extended_stats, original_stats):
    """Compare extended results with original 21 computations"""
    print("\n" + "=" * 80)
    print("COMPARISON: Extended vs Original (21 computations)")
    print("=" * 80)
    
    print(f"\nSample Size:")
    print(f"  Original:  {original_stats['n']} computations")
    print(f"  Extended:  {extended_stats['n']} computations")
    print(f"  Increase:  {extended_stats['n']/original_stats['n']:.1f}x")
    
    print(f"\nMean Correlation (rho):")
    print(f"  Original:  {original_stats['rho_mean']:.6f} ± {original_stats['rho_std']:.6f}")
    print(f"  Extended:  {extended_stats['rho_mean']:.6f} ± {extended_stats['rho_std']:.6f}")
    diff = abs(extended_stats['rho_mean'] - original_stats['rho_mean'])
    print(f"  Difference: {diff:.6f} ({100*diff/original_stats['rho_mean']:.2f}% relative)")
    
    print(f"\nMean Cancellation Constant (K):")
    print(f"  Original:  {original_stats['K_mean']:.6f} ± {original_stats['K_std']:.6f}")
    print(f"  Extended:  {extended_stats['K_mean']:.6f} ± {extended_stats['K_std']:.6f}")
    diff = abs(extended_stats['K_mean'] - original_stats['K_mean'])
    print(f"  Difference: {diff:.6f} ({100*diff/original_stats['K_mean']:.2f}% relative)")
    
    print(f"\nHigh Correlation Cases (rho > 0.8):")
    print(f"  Original:  {original_stats.get('high_corr_pct', 0):.1f}%")
    print(f"  Extended:  {extended_stats['high_corr_pct']:.1f}%")
    
    print(f"\nConclusion:")
    if diff < 0.1:
        print(f"  [OK] Extended results are consistent with original (difference < 10%)")
        print(f"  [OK] Larger sample size ({extended_stats['n']} vs {original_stats['n']}) provides more robust statistics")
    else:
        print(f"  [WARN] Extended results differ from original by > 10%")
        print(f"  [INFO] This may indicate sample size effects or parameter sensitivity")

if __name__ == "__main__":
    # Load original results
    try:
        original = load_results("computation_results.json")
        original_stats = analyze_statistics(original)
        print("\n" + "=" * 80)
        print("ORIGINAL RESULTS (21 computations)")
        print("=" * 80)
    except FileNotFoundError:
        print("Original results not found, skipping comparison")
        original_stats = None
    
    # Load extended results
    try:
        extended = load_results("extended_computation_results.json")
        extended_stats = analyze_statistics(extended)
        print("\n" + "=" * 80)
        print("EXTENDED RESULTS")
        print("=" * 80)
        
        if original_stats:
            compare_with_original(extended_stats, original_stats)
    except FileNotFoundError:
        print("Extended results not found. Run extended_benchmark.py first.")
