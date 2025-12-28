"""
Massive 100,000 Simulations: Maximum statistical robustness
Optimized for large-scale computation with checkpointing and progress tracking
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import numpy as np
from real_iut_construction import construct_hodge_theater_step_by_step, EllipticCurve, compute_correlation_real
import time
import random
from datetime import datetime
import io
import contextlib

# Generate diverse parameter space
def generate_curves_pool(n=200):
    """Generate pool of n diverse elliptic curves"""
    curves = []
    for a in range(-10, 11):
        for b in range(-10, 11):
            for c in range(-5, 6):
                if len(curves) >= n:
                    break
                curves.append({
                    "a": a,
                    "b": b,
                    "c": c,
                    "name": f"y^2 = x^3 + {a if a != 0 else ''}{'x^2' if a != 0 else ''}{'+' if b > 0 and a != 0 else '' if b == 0 or a == 0 else '-'}{abs(b) if b != 0 else ''}x{' + ' if c > 0 else ' - ' if c < 0 else ''}{abs(c) if c != 0 else ''}".replace('  ', ' ').strip()
                })
            if len(curves) >= n:
                break
        if len(curves) >= n:
            break
    return curves[:n]

def generate_primes_pool(n=200):
    """Generate pool of n primes"""
    primes = []
    num = 2
    while len(primes) < n:
        is_prime = True
        for p in primes:
            if p * p > num:
                break
            if num % p == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(num)
        num += 1
    return primes

def compute_single_simulation(curve_dict, prime):
    """Compute single simulation, return result or None on error"""
    try:
        ec = EllipticCurve(a=curve_dict["a"], b=curve_dict["b"], c=curve_dict["c"])
        
        # Suppress output for speed
        with contextlib.redirect_stdout(io.StringIO()):
            hodge_theater = construct_hodge_theater_step_by_step(ec, prime, l=13)
            rho, stats_dict = compute_correlation_real(hodge_theater)
        
        return {
            "curve": curve_dict,
            "prime": prime,
            "steps": hodge_theater.steps,
            "rho": float(rho),
            "K": float(stats_dict["K"]),
            "cov": float(stats_dict["cov"]),
            "var_11": float(stats_dict["var_11"]),
            "var_22": float(stats_dict["var_22"]),
            "mean_11": float(stats_dict["mean_11"]),
            "mean_22": float(stats_dict["mean_22"]),
            "n": len(hodge_theater.diagonal_errors_11)
        }
    except Exception as e:
        return None

def compute_100k_simulations():
    """Compute 100,000 simulations"""
    TOTAL_SIMULATIONS = 100000
    
    # Generate parameter pools
    print("=" * 80)
    print("MASSIVE 100,000 SIMULATIONS")
    print("=" * 80)
    print(f"Generating parameter pools...")
    
    curves_pool = generate_curves_pool(200)
    primes_pool = generate_primes_pool(200)
    
    print(f"  Curves pool: {len(curves_pool)} curves")
    print(f"  Primes pool: {len(primes_pool)} primes")
    print(f"  Total combinations: {len(curves_pool) * len(primes_pool)}")
    print()
    
    # Results storage
    results = []
    start_time = time.time()
    
    # Checkpoint settings
    checkpoint_interval = 1000
    last_checkpoint = 0
    
    print(f"Starting {TOTAL_SIMULATIONS} simulations...")
    print(f"Checkpoints every {checkpoint_interval} simulations")
    print("=" * 80)
    print()
    
    # Progress tracking
    successful = 0
    failed = 0
    
    for i in range(TOTAL_SIMULATIONS):
        # Random sampling from pools
        curve = random.choice(curves_pool)
        prime = random.choice(primes_pool)
        
        # Compute simulation
        result = compute_single_simulation(curve, prime)
        
        if result is not None:
            results.append(result)
            successful += 1
        else:
            failed += 1
        
        # Progress reporting
        if (i + 1) % 100 == 0:
            elapsed = time.time() - start_time
            rate = (i + 1) / elapsed if elapsed > 0 else 0
            remaining = (TOTAL_SIMULATIONS - i - 1) / rate if rate > 0 else 0
            progress = 100 * (i + 1) / TOTAL_SIMULATIONS
            
            print(f"[{i+1:6d}/{TOTAL_SIMULATIONS}] "
                  f"Progress: {progress:5.1f}% | "
                  f"Success: {successful:6d} | "
                  f"Failed: {failed:4d} | "
                  f"Rate: {rate:5.1f} sim/s | "
                  f"ETA: {remaining/60:6.1f} min")
        
        # Checkpoint save
        if (i + 1) % checkpoint_interval == 0:
            checkpoint_time = time.time()
            checkpoint_file = f"100k_simulations_checkpoint_{i+1}.json"
            
            with open(checkpoint_file, "w") as f:
                json.dump({
                    "total_simulations": TOTAL_SIMULATIONS,
                    "completed": i + 1,
                    "successful": successful,
                    "failed": failed,
                    "timestamp": datetime.now().isoformat(),
                    "results": results
                }, f, indent=2)
            
            checkpoint_duration = time.time() - checkpoint_time
            print(f"\n[CHECKPOINT] Saved {i+1} simulations to {checkpoint_file} "
                  f"({checkpoint_duration:.2f}s)")
            print()
    
    # Final save
    print("\n" + "=" * 80)
    print("FINALIZING...")
    print("=" * 80)
    
    final_file = "100k_simulations_results.json"
    with open(final_file, "w") as f:
        json.dump({
            "total_simulations": TOTAL_SIMULATIONS,
            "successful": successful,
            "failed": failed,
            "success_rate": 100 * successful / TOTAL_SIMULATIONS,
            "timestamp": datetime.now().isoformat(),
            "results": results
        }, f, indent=2)
    
    # Statistical analysis
    if len(results) > 0:
        rhos = [r["rho"] for r in results]
        Ks = [r["K"] for r in results]
        
        print(f"\n{'='*80}")
        print(f"MASSIVE 100K SIMULATIONS - FINAL STATISTICS")
        print(f"{'='*80}")
        print(f"Total simulations: {TOTAL_SIMULATIONS}")
        print(f"Successful: {successful} ({100*successful/TOTAL_SIMULATIONS:.2f}%)")
        print(f"Failed: {failed} ({100*failed/TOTAL_SIMULATIONS:.2f}%)")
        
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
        
        # Framework validity
        K_valid = sum(1 for k in Ks if k >= 1.0)
        print(f"\nFramework Validity:")
        print(f"  K >= 1: {K_valid}/{len(results)} ({100*K_valid/len(results):.1f}%)")
        
        # Total time
        total_time = time.time() - start_time
        print(f"\nTotal time: {total_time/60:.2f} minutes ({total_time:.2f} seconds)")
        print(f"Average rate: {TOTAL_SIMULATIONS/total_time:.2f} simulations/second")
        
        print(f"\nResults saved to {final_file}")
        print(f"{'='*80}")
    
    return results

if __name__ == "__main__":
    print("=" * 80)
    print("MASSIVE 100,000 SIMULATIONS")
    print("=" * 80)
    print("This will perform 100,000 IUT constructions across diverse curves and primes.")
    print("Progress will be saved every 1000 simulations (checkpoints).")
    print("Estimated time: Several hours (depending on system performance).")
    print()
    print("Press Ctrl+C to stop (checkpoints will be saved).")
    print()
    
    try:
        results = compute_100k_simulations()
        print("\n✅ 100,000 simulations completed successfully!")
    except KeyboardInterrupt:
        print("\n\n⚠️  Interrupted by user. Checkpoints have been saved.")
        print("You can resume by loading the latest checkpoint file.")
    except Exception as e:
        print(f"\n\n❌ Error: {e}")
        print("Checkpoints have been saved. You can analyze partial results.")
