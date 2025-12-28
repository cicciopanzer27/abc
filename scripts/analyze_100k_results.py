"""
Analyze 100k simulations results
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import numpy as np
from scipy import stats

def load_100k_results():
    """Load 100k simulations results"""
    try:
        with open("100k_simulations_results.json", 'r') as f:
            data = json.load(f)
        return data['results']
    except FileNotFoundError:
        print("Final results not found. Checking checkpoints...")
        import glob
        checkpoints = sorted(glob.glob("100k_simulations_checkpoint_*.json"))
        if checkpoints:
            latest = checkpoints[-1]
            print(f"Loading latest checkpoint: {latest}")
            with open(latest, 'r') as f:
                data = json.load(f)
            return data['results']
        return None

def comprehensive_analysis(results):
    """Comprehensive statistical analysis"""
    if results is None or len(results) == 0:
        print("No results available")
        return
    
    print("=" * 80)
    print(f"COMPREHENSIVE ANALYSIS: {len(results)} SIMULATIONS")
    print("=" * 80)
    
    rhos = [r["rho"] for r in results]
    Ks = [r["K"] for r in results]
    
    # Basic statistics
    print(f"\n1. BASIC STATISTICS")
    print(f"   Total simulations: {len(results)}")
    print(f"   Mean ρ: {np.mean(rhos):.6f}")
    print(f"   Std ρ: {np.std(rhos):.6f}")
    print(f"   Mean K: {np.mean(Ks):.6f}")
    print(f"   Std K: {np.std(Ks):.6f}")
    
    # Distribution analysis
    print(f"\n2. DISTRIBUTION ANALYSIS")
    high_corr = sum(1 for r in rhos if r > 0.8)
    medium_corr = sum(1 for r in rhos if 0.3 <= r <= 0.8)
    low_corr = sum(1 for r in rhos if 0 <= r < 0.3)
    zero_corr = sum(1 for r in rhos if abs(r) < 0.01)
    
    print(f"   High correlation (ρ > 0.8): {high_corr}/{len(results)} ({100*high_corr/len(results):.2f}%)")
    print(f"   Medium correlation (0.3 ≤ ρ ≤ 0.8): {medium_corr}/{len(results)} ({100*medium_corr/len(results):.2f}%)")
    print(f"   Low correlation (0 ≤ ρ < 0.3): {low_corr}/{len(results)} ({100*low_corr/len(results):.2f}%)")
    print(f"   Near-zero correlation (|ρ| < 0.01): {zero_corr}/{len(results)} ({100*zero_corr/len(results):.2f}%)")
    
    # Percentiles
    print(f"\n3. PERCENTILES")
    for p in [5, 10, 25, 50, 75, 90, 95]:
        print(f"   {p}th percentile ρ: {np.percentile(rhos, p):.6f}")
        print(f"   {p}th percentile K: {np.percentile(Ks, p):.6f}")
    
    # Framework validity
    print(f"\n4. FRAMEWORK VALIDITY")
    K_valid = sum(1 for k in Ks if k >= 1.0)
    K_optimal = sum(1 for k in Ks if 1.0 <= k <= 2.0)
    print(f"   K ≥ 1: {K_valid}/{len(results)} ({100*K_valid/len(results):.2f}%)")
    print(f"   1 ≤ K ≤ 2 (optimal): {K_optimal}/{len(results)} ({100*K_optimal/len(results):.2f}%)")
    
    # Confidence intervals
    print(f"\n5. CONFIDENCE INTERVALS (95%)")
    rho_ci = stats.t.interval(0.95, len(rhos)-1, loc=np.mean(rhos), scale=stats.sem(rhos))
    K_ci = stats.t.interval(0.95, len(Ks)-1, loc=np.mean(Ks), scale=stats.sem(Ks))
    print(f"   ρ: [{rho_ci[0]:.6f}, {rho_ci[1]:.6f}]")
    print(f"   K: [{K_ci[0]:.6f}, {K_ci[1]:.6f}]")
    
    # Comparison with previous datasets
    print(f"\n6. COMPARISON WITH PREVIOUS DATASETS")
    previous_means = {
        "Original (21)": 0.759972,
        "ABC Triple (23)": 0.905023,
        "Extended (300)": 0.706235
    }
    
    current_mean = np.mean(rhos)
    print(f"   Current (100k): {current_mean:.6f}")
    for name, prev_mean in previous_means.items():
        diff = abs(current_mean - prev_mean)
        pct_diff = 100 * diff / prev_mean
        print(f"   {name}: {prev_mean:.6f} (diff: {diff:.6f}, {pct_diff:.2f}%)")
    
    # Save summary
    summary = {
        "n": len(results),
        "rho_mean": float(np.mean(rhos)),
        "rho_std": float(np.std(rhos)),
        "rho_median": float(np.median(rhos)),
        "K_mean": float(np.mean(Ks)),
        "K_std": float(np.std(Ks)),
        "K_median": float(np.median(Ks)),
        "high_corr_pct": 100*high_corr/len(results),
        "zero_corr_pct": 100*zero_corr/len(results),
        "K_valid_pct": 100*K_valid/len(results),
        "rho_ci_95": [float(rho_ci[0]), float(rho_ci[1])],
        "K_ci_95": [float(K_ci[0]), float(K_ci[1])]
    }
    
    with open("100k_analysis_summary.json", "w") as f:
        json.dump(summary, f, indent=2)
    
    print(f"\n✅ Analysis summary saved to 100k_analysis_summary.json")
    print("=" * 80)

if __name__ == "__main__":
    results = load_100k_results()
    if results:
        comprehensive_analysis(results)
    else:
        print("No results found. Run massive_100k_simulations.py first.")
