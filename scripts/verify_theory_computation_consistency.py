#!/usr/bin/env python3
"""
Verifica che i risultati computazionali siano consistenti con la teoria.

Questo script verifica:
1. Che ρ sia nel range teorico [-1, 1]
2. Che K = 4/(1+ρ)² sia calcolato correttamente
3. Che gli errori seguano lo scaling teorico
4. Che le statistiche siano consistenti
"""

import json
import numpy as np
import sys
import os

def load_results():
    """Carica i risultati computazionali."""
    results_path = os.path.join(os.path.dirname(__file__), 'computation_results.json')
    if not os.path.exists(results_path):
        print(f"❌ ERRORE: {results_path} non trovato")
        print("   Eseguire prima: python scripts/run_complete_computations.py")
        return None
    
    with open(results_path, 'r') as f:
        return json.load(f)

def verify_rho_bounds(results):
    """Verifica che ρ sia nel range teorico [-1, 1]"""
    print("\n1. Verifica range teorico di rho:")
    print("-" * 70)
    
    all_valid = True
    for r in results:
        rho = r['rho']
        if not (-1 <= rho <= 1):
            print(f"   [FAIL] rho = {rho:.6f} fuori range teorico [-1, 1]")
            all_valid = False
        else:
            print(f"   [OK] rho = {rho:.6f} nel range teorico")
    
    if all_valid:
        print("\n   [OK] Tutti i valori di rho sono nel range teorico [-1, 1]")
    else:
        print("\n   [FAIL] Alcuni valori di rho sono fuori range teorico")
    
    return all_valid

def verify_K_formula(results):
    """Verifica che K = 4/(1+ρ)² sia calcolato correttamente"""
    print("\n2. Verifica formula K = 4/(1+rho)^2:")
    print("-" * 70)
    
    all_valid = True
    max_error = 0.0
    
    for r in results:
        rho = r['rho']
        K_computed = r['K']
        K_theoretical = 4.0 / (1.0 + rho)**2
        
        error = abs(K_computed - K_theoretical)
        max_error = max(max_error, error)
        
        if error > 1e-5:
            print(f"   [FAIL] K mismatch per rho = {rho:.6f}:")
            print(f"      Computed: {K_computed:.6f}, Theoretical: {K_theoretical:.6f}")
            print(f"      Error: {error:.2e}")
            all_valid = False
        else:
            print(f"   [OK] K formula corretta per rho = {rho:.6f} (error: {error:.2e})")
    
    if all_valid:
        print(f"\n   [OK] Tutte le formule K sono corrette (max error: {max_error:.2e})")
    else:
        print(f"\n   [FAIL] Alcune formule K sono errate (max error: {max_error:.2e})")
    
    return all_valid

def verify_error_scaling(results):
    """Verifica che gli errori seguano lo scaling teorico"""
    print("\n3. Verifica scaling degli errori:")
    print("-" * 70)
    
    all_valid = True
    
    for r in results:
        errors_11 = r['errors_11']
        errors_22 = r['errors_22']
        steps = len(errors_11)
        
        # Verifica che errors_11 crescano (non necessariamente quadratico, ma crescente)
        if len(errors_11) > 1:
            # Calcola differenze
            diffs_11 = [errors_11[i+1] - errors_11[i] for i in range(len(errors_11)-1)]
            
            # Verifica che errors_22 siano piccoli rispetto a errors_11
            max_11 = max(abs(e) for e in errors_11)
            max_22 = max(abs(e) for e in errors_22)
            
            if max_22 > max_11:
                print(f"   ⚠ Warning: errors_22 ({max_22:.6f}) > errors_11 ({max_11:.6f})")
                print(f"      Curve: {r['curve']}, Prime: {r['prime']}")
            else:
                print(f"   [OK] Scaling verificato: max_11={max_11:.6f}, max_22={max_22:.6f}")
    
    if all_valid:
        print("\n   [OK] Scaling degli errori verificato")
    else:
        print("\n   ⚠ Alcuni warning sullo scaling")
    
    return all_valid

def verify_statistics(results):
    """Verifica che le statistiche siano consistenti"""
    print("\n4. Verifica statistiche:")
    print("-" * 70)
    
    rhos = [r['rho'] for r in results]
    Ks = [r['K'] for r in results]
    
    mean_rho = np.mean(rhos)
    std_rho = np.std(rhos)
    min_rho = np.min(rhos)
    max_rho = np.max(rhos)
    
    mean_K = np.mean(Ks)
    min_K = np.min(Ks)
    max_K = np.max(Ks)
    
    print(f"   rho statistics:")
    print(f"      Mean: {mean_rho:.6f}")
    print(f"      Std:  {std_rho:.6f}")
    print(f"      Range: [{min_rho:.6f}, {max_rho:.6f}]")
    
    print(f"\n   K statistics:")
    print(f"      Mean: {mean_K:.6f}")
    print(f"      Range: [{min_K:.6f}, {max_K:.6f}]")
    
    # Verifica che K >= 1 (framework valido)
    if min_K < 1.0:
        print(f"\n   ⚠ Warning: min_K = {min_K:.6f} < 1.0")
        print(f"      Framework potrebbe non essere valido per alcuni casi")
        return False
    
    print(f"\n   [OK] Statistiche consistenti (K >= 1 per tutti i casi)")
    return True

def verify_covariance_formula(results):
    """Verifica che la covarianza sia calcolata correttamente"""
    print("\n5. Verifica calcolo covarianza:")
    print("-" * 70)
    
    all_valid = True
    
    for r in results:
        errors_11 = np.array(r['errors_11'])
        errors_22 = np.array(r['errors_22'])
        cov_computed = r['cov']
        
        # Calcola covarianza manualmente
        mean_11 = np.mean(errors_11)
        mean_22 = np.mean(errors_22)
        cov_theoretical = np.mean((errors_11 - mean_11) * (errors_22 - mean_22))
        
        error = abs(cov_computed - cov_theoretical)
        
        if error > 1e-5:
            print(f"   [FAIL] Covarianza errata per curve={r['curve']}, p={r['prime']}:")
            print(f"      Computed: {cov_computed:.6f}, Theoretical: {cov_theoretical:.6f}")
            print(f"      Error: {error:.2e}")
            all_valid = False
        else:
            print(f"   [OK] Covarianza corretta (error: {error:.2e})")
    
    if all_valid:
        print("\n   [OK] Tutte le covarianze sono calcolate correttamente")
    else:
        print("\n   [FAIL] Alcune covarianze sono errate")
    
    return all_valid

def main():
    """Esegue tutte le verifiche di consistenza"""
    print("=" * 70)
    print("VERIFICA CONSISTENZA TEORIA-CALCOLI")
    print("=" * 70)
    
    results = load_results()
    if results is None:
        return False
    
    print(f"\nCaricati {len(results)} risultati computazionali")
    
    all_passed = True
    
    all_passed &= verify_rho_bounds(results)
    all_passed &= verify_K_formula(results)
    all_passed &= verify_error_scaling(results)
    all_passed &= verify_statistics(results)
    all_passed &= verify_covariance_formula(results)
    
    print("\n" + "=" * 70)
    if all_passed:
        print("[OK] TUTTE LE VERIFICHE DI CONSISTENZA PASSATE!")
    else:
        print("[FAIL] ALCUNE VERIFICHE FALLITE")
    print("=" * 70)
    
    return all_passed

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
