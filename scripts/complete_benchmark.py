#!/usr/bin/env python3
"""
COMPLETE Benchmark with Real IUT Construction

This script runs complete, step-by-step IUT constructions for multiple
curves and primes, computing real correlation coefficients.
"""

import sys
sys.path.append('scripts')
from real_iut_construction import (
    EllipticCurve, construct_hodge_theater_step_by_step, 
    compute_correlation_real
)

def run_complete_benchmark():
    """Run complete benchmark with real constructions."""
    print("="*70)
    print("COMPLETE BENCHMARK - REAL IUT CONSTRUCTION")
    print("="*70)
    
    curves = [
        EllipticCurve(0, 1, 1),  # y² = x³ + x + 1
        EllipticCurve(0, 0, 1),  # y² = x³ + 1
        EllipticCurve(0, -1, 1), # y² = x³ - x + 1
    ]
    
    primes = [5, 7, 11, 13, 17, 19, 23]
    
    results = []
    
    for curve in curves:
        for p in primes:
            print(f"\n{'='*70}")
            print(f"Curve: y² = x³ + {curve.a}x² + {curve.b}x + {curve.c}")
            print(f"Prime: p = {p}")
            print(f"{'='*70}")
            
            try:
                # Real construction
                hodge_theater = construct_hodge_theater_step_by_step(curve, p, 13)
                
                # Real correlation computation
                rho, stats = compute_correlation_real(hodge_theater)
                
                results.append({
                    'curve': f"y² = x³ + {curve.a}x² + {curve.b}x + {curve.c}",
                    'prime': p,
                    'rho': rho,
                    'K': stats['K'],
                    'cov': stats['cov'],
                    'var_11': stats['var_11'],
                    'var_22': stats['var_22']
                })
                
                print(f"\n[RESULT] ρ = {rho:.6f}, K = {stats['K']:.6f}")
                
            except Exception as e:
                print(f"[ERROR] {e}")
                continue
    
    # Summary
    print(f"\n{'='*70}")
    print("BENCHMARK SUMMARY")
    print(f"{'='*70}")
    print(f"{'Curve':<30} {'Prime':<8} {'Rho':<12} {'K':<12}")
    print("-"*70)
    
    for r in results:
        curve_str = r['curve'][:28]
        print(f"{curve_str:<30} {r['prime']:>8}  {r['rho']:>10.6f}  {r['K']:>10.6f}")
    
    print("-"*70)
    
    if results:
        mean_rho = sum(r['rho'] for r in results) / len(results)
        mean_K = sum(r['K'] for r in results) / len(results)
        
        print(f"\nMean ρ: {mean_rho:.6f}")
        print(f"Mean K: {mean_K:.6f}")
        print(f"Total computations: {len(results)}")
    
    print("="*70)
    
    return results

if __name__ == "__main__":
    results = run_complete_benchmark()
