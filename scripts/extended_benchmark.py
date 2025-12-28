"""
Extended Benchmark: More primes, more curves, more comprehensive analysis
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import numpy as np
from real_iut_construction import construct_hodge_theater_step_by_step, EllipticCurve, compute_correlation_real
import numpy as np

def compute_correlation_from_errors(errors_11, errors_22):
    """Compute correlation coefficient from error sequences"""
    if len(errors_11) != len(errors_22) or len(errors_11) < 2:
        return 0.0, 4.0, 0.0, 0.0, 0.0, 0.0, 0.0
    
    mean_11 = np.mean(errors_11)
    mean_22 = np.mean(errors_22)
    
    cov = np.mean([(errors_11[i] - mean_11) * (errors_22[i] - mean_22) for i in range(len(errors_11))])
    var_11 = np.var(errors_11)
    var_22 = np.var(errors_22)
    
    if var_11 == 0 or var_22 == 0:
        rho = 0.0
    else:
        rho = cov / np.sqrt(var_11 * var_22)
    
    K = 4.0 / ((1.0 + rho) ** 2) if rho != -1.0 else float('inf')
    
    return rho, K, cov, var_11, var_22, mean_11, mean_22

# Extended set of primes
PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127]

# Extended set of elliptic curves
CURVES = [
    {"a": 0, "b": 1, "c": 1, "name": "y^2 = x^3 + x + 1"},
    {"a": 0, "b": 0, "c": 1, "name": "y^2 = x^3 + 1"},
    {"a": 0, "b": -1, "c": 1, "name": "y^2 = x^3 - x + 1"},
    {"a": 1, "b": 0, "c": 0, "name": "y^2 = x^3 + x"},
    {"a": -1, "b": 0, "c": 0, "name": "y^2 = x^3 - x"},
    {"a": 0, "b": 2, "c": 1, "name": "y^2 = x^3 + 2x + 1"},
    {"a": 0, "b": -2, "c": 1, "name": "y^2 = x^3 - 2x + 1"},
    {"a": 1, "b": 1, "c": 0, "name": "y^2 = x^3 + x^2 + x"},
    {"a": -1, "b": 1, "c": 0, "name": "y^2 = x^3 - x^2 + x"},
    {"a": 0, "b": 3, "c": 1, "name": "y^2 = x^3 + 3x + 1"},
]

def compute_extended_benchmark():
    """Compute benchmark across extended set of primes and curves"""
    results = []
    
    total = len(CURVES) * len(PRIMES)
    current = 0
    
    print(f"Extended Benchmark: {len(CURVES)} curves x {len(PRIMES)} primes = {total} computations")
    print("=" * 80)
    
    for curve in CURVES:
        for prime in PRIMES:
            current += 1
            try:
                print(f"[{current}/{total}] Curve: {curve['name']}, Prime: {prime}...", end=" ")
                
                # Construct Hodge theater
                ec = EllipticCurve(a=curve["a"], b=curve["b"], c=curve["c"])
                hodge_theater = construct_hodge_theater_step_by_step(
                    ec, prime, l=13
                )
                
                # Compute correlation
                rho, stats_dict = compute_correlation_real(hodge_theater)
                K = stats_dict["K"]
                cov = stats_dict["cov"]
                var_11 = stats_dict["var_11"]
                var_22 = stats_dict["var_22"]
                mean_11 = stats_dict["mean_11"]
                mean_22 = stats_dict["mean_22"]
                
                result_data = {
                    "curve": curve,
                    "prime": prime,
                    "steps": hodge_theater.steps,
                    "rho": float(rho),
                    "K": float(K),
                    "cov": float(cov),
                    "var_11": float(var_11),
                    "var_22": float(var_22),
                    "mean_11": float(mean_11),
                    "mean_22": float(mean_22),
                    "n": len(hodge_theater.diagonal_errors_11),
                    "errors_11": [float(e) for e in hodge_theater.diagonal_errors_11],
                    "errors_22": [float(e) for e in hodge_theater.diagonal_errors_22]
                }
                
                results.append(result_data)
                print(f"rho={rho:.6f}, K={K:.6f}")
                
            except Exception as e:
                print(f"ERROR: {e}")
                continue
    
    # Save results
    with open("extended_computation_results.json", "w") as f:
        json.dump(results, f, indent=2)
    
    # Statistical analysis
    rhos = [r["rho"] for r in results]
    Ks = [r["K"] for r in results]
    
    print("\n" + "=" * 80)
    print("EXTENDED BENCHMARK STATISTICS")
    print("=" * 80)
    print(f"Total computations: {len(results)}")
    print(f"\nCorrelation (rho):")
    print(f"  Mean: {np.mean(rhos):.6f}")
    print(f"  Std:  {np.std(rhos):.6f}")
    print(f"  Min:  {np.min(rhos):.6f}")
    print(f"  Max:  {np.max(rhos):.6f}")
    print(f"  Median: {np.median(rhos):.6f}")
    print(f"\nCancellation Constant (K):")
    print(f"  Mean: {np.mean(Ks):.6f}")
    print(f"  Std:  {np.std(Ks):.6f}")
    print(f"  Min:  {np.min(Ks):.6f}")
    print(f"  Max:  {np.max(Ks):.6f}")
    print(f"  Median: {np.median(Ks):.6f}")
    
    # Analysis by prime
    print(f"\nAnalysis by Prime:")
    for prime in sorted(set(r["prime"] for r in results)):
        prime_rhos = [r["rho"] for r in results if r["prime"] == prime]
        if prime_rhos:
            print(f"  p={prime:3d}: mean_rho={np.mean(prime_rhos):.6f}, std={np.std(prime_rhos):.6f}, n={len(prime_rhos)}")
    
    # Analysis by curve
    print(f"\nAnalysis by Curve:")
    for curve in CURVES:
        curve_rhos = [r["rho"] for r in results if r["curve"]["name"] == curve["name"]]
        if curve_rhos:
            print(f"  {curve['name']:30s}: mean_rho={np.mean(curve_rhos):.6f}, std={np.std(curve_rhos):.6f}, n={len(curve_rhos)}")
    
    return results

if __name__ == "__main__":
    results = compute_extended_benchmark()
    print(f"\nResults saved to extended_computation_results.json")
