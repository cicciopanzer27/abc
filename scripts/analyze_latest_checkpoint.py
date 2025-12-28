"""
Analyze latest valid checkpoint from 100k simulations
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import glob
import numpy as np

def find_latest_valid_checkpoint():
    """Find latest valid checkpoint"""
    checkpoints = glob.glob("100k_simulations_checkpoint_*.json")
    if not checkpoints:
        return None
    
    # Sort by number
    def get_number(filename):
        try:
            return int(filename.split('_')[-1].replace('.json', ''))
        except:
            return 0
    
    sorted_checkpoints = sorted(checkpoints, key=get_number, reverse=True)
    
    # Find first valid one
    for checkpoint in sorted_checkpoints:
        try:
            with open(checkpoint, 'r') as f:
                data = json.load(f)
            if 'results' in data and len(data['results']) > 0:
                return checkpoint, data
        except:
            continue
    
    return None

def analyze_checkpoint(checkpoint_file, data):
    """Analyze checkpoint data"""
    print("=" * 80)
    print(f"ANALYSIS OF CHECKPOINT: {checkpoint_file}")
    print("=" * 80)
    
    print(f"\nProgress:")
    print(f"  Completed: {data['completed']}/{data['total_simulations']} "
          f"({100*data['completed']/data['total_simulations']:.2f}%)")
    print(f"  Successful: {data['successful']}")
    print(f"  Failed: {data['failed']}")
    print(f"  Success rate: {100*data['successful']/data['completed']:.2f}%")
    
    if len(data['results']) == 0:
        print("\nNo results in checkpoint")
        return
    
    results = data['results']
    rhos = [r['rho'] for r in results]
    Ks = [r['K'] for r in results]
    
    print(f"\n{'='*80}")
    print(f"STATISTICAL ANALYSIS ({len(results)} simulations)")
    print(f"{'='*80}")
    
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
    print(f"  High correlation (ρ > 0.8): {high_corr}/{len(results)} ({100*high_corr/len(results):.2f}%)")
    print(f"  Medium correlation (0.3 ≤ ρ ≤ 0.8): {medium_corr}/{len(results)} ({100*medium_corr/len(results):.2f}%)")
    print(f"  Low correlation (0 ≤ ρ < 0.3): {low_corr}/{len(results)} ({100*low_corr/len(results):.2f}%)")
    print(f"  Near-zero correlation (|ρ| < 0.01): {zero_corr}/{len(results)} ({100*zero_corr/len(results):.2f}%)")
    
    # Framework validity
    K_valid = sum(1 for k in Ks if k >= 1.0)
    print(f"\nFramework Validity:")
    print(f"  K ≥ 1: {K_valid}/{len(results)} ({100*K_valid/len(results):.1f}%)")
    
    # Comparison with previous
    previous_means = {
        "Original (21)": 0.759972,
        "ABC Triple (23)": 0.905023,
        "Extended (300)": 0.706235
    }
    
    current_mean = np.mean(rhos)
    print(f"\nComparison with Previous Datasets:")
    print(f"  Current (100k partial): {current_mean:.6f}")
    for name, prev_mean in previous_means.items():
        diff = abs(current_mean - prev_mean)
        pct_diff = 100 * diff / prev_mean if prev_mean > 0 else 0
        status = "✓" if diff < 0.1 else "⚠"
        print(f"  {status} {name}: {prev_mean:.6f} (diff: {diff:.6f}, {pct_diff:.2f}%)")
    
    print(f"\n{'='*80}")

if __name__ == "__main__":
    result = find_latest_valid_checkpoint()
    if result:
        checkpoint_file, data = result
        analyze_checkpoint(checkpoint_file, data)
    else:
        print("No valid checkpoint found")
