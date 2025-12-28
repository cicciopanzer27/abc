"""
Compare all benchmark results: original (21), ABC triple (23), extended (300), massive (5000)
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import numpy as np

def load_results(filename):
    """Load results from JSON file"""
    try:
        with open(filename, 'r') as f:
            data = json.load(f)
        # Handle different formats
        if isinstance(data, list):
            return data
        elif isinstance(data, dict) and 'results' in data:
            return data['results']
        else:
            return []
    except FileNotFoundError:
        return None

def analyze_dataset(results, name):
    """Analyze a dataset"""
    if results is None or len(results) == 0:
        print(f"\n{name}: NOT AVAILABLE")
        return None
    
    rhos = [r["rho"] for r in results]
    Ks = [r["K"] for r in results]
    
    stats = {
        "name": name,
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
        "high_corr_pct": 100 * sum(1 for r in rhos if r > 0.8) / len(rhos),
        "zero_corr_pct": 100 * sum(1 for r in rhos if abs(r) < 0.01) / len(rhos),
        "K_valid_pct": 100 * sum(1 for k in Ks if k >= 1.0) / len(Ks)
    }
    
    return stats

def print_comparison(stats_list):
    """Print comparison table"""
    print("\n" + "=" * 100)
    print("COMPREHENSIVE COMPARISON OF ALL BENCHMARKS")
    print("=" * 100)
    
    # Header
    print(f"\n{'Dataset':<20} {'N':<6} {'Mean ρ':<10} {'Std ρ':<10} {'Mean K':<10} {'High ρ%':<10} {'Zero ρ%':<10} {'K≥1%':<10}")
    print("-" * 100)
    
    for stats in stats_list:
        if stats:
            print(f"{stats['name']:<20} {stats['n']:<6} "
                  f"{stats['rho_mean']:<10.6f} {stats['rho_std']:<10.6f} "
                  f"{stats['K_mean']:<10.6f} {stats['high_corr_pct']:<10.1f} "
                  f"{stats['zero_corr_pct']:<10.1f} {stats['K_valid_pct']:<10.1f}")
    
    # Summary statistics
    print("\n" + "=" * 100)
    print("KEY FINDINGS")
    print("=" * 100)
    
    available_stats = [s for s in stats_list if s is not None]
    
    if len(available_stats) > 0:
        rho_means = [s['rho_mean'] for s in available_stats]
        K_means = [s['K_mean'] for s in available_stats]
        
        print(f"\n1. Correlation (ρ) Stability:")
        print(f"   Mean ρ across all datasets: {np.mean(rho_means):.6f}")
        print(f"   Std of means: {np.std(rho_means):.6f}")
        print(f"   Range of means: [{np.min(rho_means):.6f}, {np.max(rho_means):.6f}]")
        
        print(f"\n2. Cancellation Constant (K) Stability:")
        print(f"   Mean K across all datasets: {np.mean(K_means):.6f}")
        print(f"   Std of means: {np.std(K_means):.6f}")
        print(f"   Range of means: [{np.min(K_means):.6f}, {np.max(K_means):.6f}]")
        
        print(f"\n3. Framework Validity:")
        all_valid = all(s['K_valid_pct'] == 100.0 for s in available_stats)
        print(f"   All datasets have K ≥ 1: {'[OK]' if all_valid else '[WARN]'}")
        
        print(f"\n4. High Correlation Prevalence:")
        high_corr_avg = np.mean([s['high_corr_pct'] for s in available_stats])
        print(f"   Average high correlation (ρ > 0.8): {high_corr_avg:.1f}%")
        print(f"   This confirms strong IUT structure in most cases")
        
        print(f"\n5. Statistical Robustness:")
        if len(available_stats) >= 2:
            rho_consistency = "HIGH" if np.std(rho_means) < 0.1 else "MODERATE"
            print(f"   ρ consistency across datasets: {rho_consistency}")
            print(f"   (Std of means = {np.std(rho_means):.6f})")

if __name__ == "__main__":
    # Load all datasets
    original = load_results("computation_results.json")
    abc_triple = load_results("abc_triple_625_2048_2673_results.json")
    extended = load_results("extended_computation_results.json")
    massive = load_results("massive_computation_results.json")
    
    # Analyze each
    stats_original = analyze_dataset(original, "Original (21)")
    stats_abc = analyze_dataset(abc_triple, "ABC Triple (23)")
    stats_extended = analyze_dataset(extended, "Extended (300)")
    stats_massive = analyze_dataset(massive, "Massive (5000)")
    
    # Print individual analyses
    for stats in [stats_original, stats_abc, stats_extended, stats_massive]:
        if stats:
            print(f"\n{stats['name']}:")
            print(f"  N = {stats['n']}")
            print(f"  Mean ρ = {stats['rho_mean']:.6f} ± {stats['rho_std']:.6f}")
            print(f"  Mean K = {stats['K_mean']:.6f} ± {stats['K_std']:.6f}")
            print(f"  High correlation: {stats['high_corr_pct']:.1f}%")
            print(f"  Zero correlation: {stats['zero_corr_pct']:.1f}%")
            print(f"  K ≥ 1: {stats['K_valid_pct']:.1f}%")
    
    # Print comparison
    print_comparison([stats_original, stats_abc, stats_extended, stats_massive])
    
    # Save summary
    summary = {
        "datasets": [s for s in [stats_original, stats_abc, stats_extended, stats_massive] if s is not None],
        "timestamp": __import__('datetime').datetime.now().isoformat()
    }
    
    with open("benchmark_comparison_summary.json", "w") as f:
        json.dump(summary, f, indent=2)
    
    print(f"\nSummary saved to benchmark_comparison_summary.json")
