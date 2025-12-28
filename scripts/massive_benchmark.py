"""
Massive Benchmark: 50 curves × 100 primes = 5000 computations
For maximum statistical robustness
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import numpy as np
from real_iut_construction import construct_hodge_theater_step_by_step, EllipticCurve, compute_correlation_real
import time

# Generate 50 diverse elliptic curves
def generate_curves():
    """Generate 50 diverse elliptic curves"""
    curves = []
    
    # Base curves
    base_curves = [
        (0, 1, 1), (0, 0, 1), (0, -1, 1), (1, 0, 0), (-1, 0, 0),
        (0, 2, 1), (0, -2, 1), (1, 1, 0), (-1, 1, 0), (0, 3, 1),
        (1, 2, 1), (-1, 2, 1), (2, 0, 1), (-2, 0, 1), (1, -1, 1),
        (0, 4, 1), (0, -4, 1), (2, 1, 1), (-2, 1, 1), (1, 3, 1),
        (0, 5, 1), (0, -5, 1), (3, 0, 1), (-3, 0, 1), (2, 2, 1),
        (0, 6, 1), (0, -6, 1), (1, 4, 1), (-1, 4, 1), (3, 1, 1),
        (0, 7, 1), (0, -7, 1), (2, 3, 1), (-2, 3, 1), (4, 0, 1),
        (0, 8, 1), (0, -8, 1), (1, 5, 1), (-1, 5, 1), (3, 2, 1),
        (0, 9, 1), (0, -9, 1), (2, 4, 1), (-2, 4, 1), (5, 0, 1),
        (0, 10, 1), (0, -10, 1), (1, 6, 1), (-1, 6, 1), (4, 1, 1)
    ]
    
    for a, b, c in base_curves[:50]:
        curves.append({
            "a": a,
            "b": b,
            "c": c,
            "name": f"y^2 = x^3 + {a if a != 0 else ''}{'x^2' if a != 0 else ''}{'+' if b > 0 and a != 0 else '' if b == 0 or a == 0 else '-'}{abs(b) if b != 0 else ''}x{' + ' if c > 0 else ' - ' if c < 0 else ''}{abs(c) if c != 0 else ''}".replace('  ', ' ').strip()
        })
    
    return curves

# Generate first 100 primes
def generate_primes():
    """Generate first 100 primes"""
    primes = []
    n = 2
    while len(primes) < 100:
        is_prime = True
        for p in primes:
            if p * p > n:
                break
            if n % p == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(n)
        n += 1
    return primes

def compute_massive_benchmark():
    """Compute massive benchmark across 50 curves and 100 primes"""
    curves = generate_curves()
    primes = generate_primes()
    
    results = []
    total = len(curves) * len(primes)
    current = 0
    start_time = time.time()
    
    print(f"Massive Benchmark: {len(curves)} curves × {len(primes)} primes = {total} computations")
    print("=" * 80)
    
    # Save progress every 100 computations
    checkpoint_interval = 100
    
    for curve in curves:
        for prime in primes:
            current += 1
            try:
                if current % 50 == 0:
                    elapsed = time.time() - start_time
                    rate = current / elapsed if elapsed > 0 else 0
                    remaining = (total - current) / rate if rate > 0 else 0
                    print(f"[{current}/{total}] {curve['name']}, p={prime}... "
                          f"({current*100/total:.1f}%, ETA: {remaining/60:.1f}min)", end=" ")
                
                # Construct Hodge theater
                ec = EllipticCurve(a=curve["a"], b=curve["b"], c=curve["c"])
                hodge_theater = construct_hodge_theater_step_by_step(
                    ec, prime, l=13
                )
                
                # Compute correlation (suppress output)
                import io
                import contextlib
                with contextlib.redirect_stdout(io.StringIO()):
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
                
                if current % 50 == 0:
                    print(f"rho={rho:.4f}, K={K:.4f}")
                
                # Checkpoint save
                if current % checkpoint_interval == 0:
                    with open("massive_computation_results_checkpoint.json", "w") as f:
                        json.dump(results, f, indent=2)
                    print(f"\n[CHECKPOINT] Saved {current} results")
                
            except Exception as e:
                if current % 50 == 0:
                    print(f"ERROR: {e}")
                continue
    
    # Final save
    with open("massive_computation_results.json", "w") as f:
        json.dump(results, f, indent=2)
    
    # Statistical analysis
    rhos = [r["rho"] for r in results]
    Ks = [r["K"] for r in results]
    
    print("\n" + "=" * 80)
    print("MASSIVE BENCHMARK STATISTICS")
    print("=" * 80)
    print(f"Total successful computations: {len(results)}/{total}")
    print(f"\nCorrelation (rho):")
    print(f"  Mean: {np.mean(rhos):.6f}")
    print(f"  Std:  {np.std(rhos):.6f}")
    print(f"  Min:  {np.min(rhos):.6f}")
    print(f"  Max:  {np.max(rhos):.6f}")
    print(f"  Median: {np.median(rhos):.6f}")
    print(f"  25th percentile: {np.percentile(rhos, 25):.6f}")
    print(f"  75th percentile: {np.percentile(rhos, 75):.6f}")
    
    print(f"\nCancellation Constant (K):")
    print(f"  Mean: {np.mean(Ks):.6f}")
    print(f"  Std:  {np.std(Ks):.6f}")
    print(f"  Min:  {np.min(Ks):.6f}")
    print(f"  Max:  {np.max(Ks):.6f}")
    print(f"  Median: {np.median(Ks):.6f}")
    
    # Distribution
    high_corr = sum(1 for r in rhos if r > 0.8)
    medium_corr = sum(1 for r in rhos if 0.3 <= r <= 0.8)
    low_corr = sum(1 for r in rhos if 0 <= r < 0.3)
    zero_corr = sum(1 for r in rhos if abs(r) < 0.01)
    
    print(f"\nDistribution:")
    print(f"  High correlation (rho > 0.8): {high_corr}/{len(results)} ({100*high_corr/len(results):.1f}%)")
    print(f"  Medium correlation (0.3 <= rho <= 0.8): {medium_corr}/{len(results)} ({100*medium_corr/len(results):.1f}%)")
    print(f"  Low correlation (0 <= rho < 0.3): {low_corr}/{len(results)} ({100*low_corr/len(results):.1f}%)")
    print(f"  Near-zero correlation (|rho| < 0.01): {zero_corr}/{len(results)} ({100*zero_corr/len(results):.1f}%)")
    
    return results

if __name__ == "__main__":
    print("Starting MASSIVE BENCHMARK (5000 computations)...")
    print("This will take significant time. Progress will be saved periodically.")
    print()
    
    results = compute_massive_benchmark()
    print(f"\nResults saved to massive_computation_results.json")
    print(f"Total: {len(results)} successful computations")
