"""
Monitor 100k simulations progress
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import glob
import os
from datetime import datetime

def find_latest_checkpoint():
    """Find latest checkpoint file"""
    checkpoints = glob.glob("100k_simulations_checkpoint_*.json")
    if not checkpoints:
        return None
    
    # Sort by number in filename
    def get_number(filename):
        try:
            return int(filename.split('_')[-1].replace('.json', ''))
        except:
            return 0
    
    latest = max(checkpoints, key=get_number)
    return latest

def monitor_progress():
    """Monitor progress of 100k simulations"""
    print("=" * 80)
    print("MONITORING 100K SIMULATIONS")
    print("=" * 80)
    
    # Check for final results
    if os.path.exists("100k_simulations_results.json"):
        print("\n✅ FINAL RESULTS FOUND!")
        with open("100k_simulations_results.json", 'r') as f:
            data = json.load(f)
        
        print(f"Total simulations: {data['total_simulations']}")
        print(f"Successful: {data['successful']}")
        print(f"Failed: {data['failed']}")
        print(f"Success rate: {data['success_rate']:.2f}%")
        print(f"Timestamp: {data['timestamp']}")
        return
    
    # Check for checkpoints
    latest_checkpoint = find_latest_checkpoint()
    if latest_checkpoint:
        print(f"\n📊 Latest checkpoint: {latest_checkpoint}")
        with open(latest_checkpoint, 'r') as f:
            data = json.load(f)
        
        print(f"Completed: {data['completed']}/{data['total_simulations']} "
              f"({100*data['completed']/data['total_simulations']:.2f}%)")
        print(f"Successful: {data['successful']}")
        print(f"Failed: {data['failed']}")
        print(f"Timestamp: {data['timestamp']}")
        
        if len(data['results']) > 0:
            import numpy as np
            rhos = [r['rho'] for r in data['results']]
            Ks = [r['K'] for r in data['results']]
            
            print(f"\nCurrent Statistics:")
            print(f"  Mean ρ: {np.mean(rhos):.6f}")
            print(f"  Mean K: {np.mean(Ks):.6f}")
            print(f"  High correlation (ρ > 0.8): {100*sum(1 for r in rhos if r > 0.8)/len(rhos):.1f}%")
    else:
        print("\n⏳ No checkpoints found yet. Simulation may be starting...")
    
    print("\n" + "=" * 80)

if __name__ == "__main__":
    monitor_progress()
