#!/usr/bin/env python3
"""
Test di regressione per verificare che modifiche non rompano risultati.

Questo script verifica che i risultati attuali siano consistenti con
una baseline di riferimento.
"""

import json
import numpy as np
import sys
import os

# Valori di riferimento (baseline)
BASELINE = {
    'mean_rho': 0.760,
    'mean_K': 1.623,
    'min_rho': 0.000,
    'max_rho': 0.959,
    'n_computations': 21,
    'tolerance_mean': 0.1,  # Tolleranza per mean
    'tolerance_range': 0.2,  # Tolleranza per range
}

def load_results():
    """Carica i risultati computazionali."""
    results_path = os.path.join(os.path.dirname(__file__), 'computation_results.json')
    if not os.path.exists(results_path):
        print(f"❌ ERRORE: {results_path} non trovato")
        print("   Eseguire prima: python scripts/run_complete_computations.py")
        return None
    
    with open(results_path, 'r') as f:
        return json.load(f)

def regression_test_statistics(results):
    """Verifica che le statistiche siano consistenti con baseline"""
    print("\n1. Test di regressione: Statistiche")
    print("-" * 70)
    
    rhos = [r['rho'] for r in results]
    Ks = [r['K'] for r in results]
    
    mean_rho = np.mean(rhos)
    mean_K = np.mean(Ks)
    min_rho = np.min(rhos)
    max_rho = np.max(rhos)
    
    all_passed = True
    
    # Verifica mean_rho
    error_mean_rho = abs(mean_rho - BASELINE['mean_rho'])
    if error_mean_rho <= BASELINE['tolerance_mean']:
        print(f"   ✓ Mean ρ: {mean_rho:.6f} (baseline: {BASELINE['mean_rho']:.6f}, error: {error_mean_rho:.6f})")
    else:
        print(f"   ❌ Mean ρ cambiato: {mean_rho:.6f} vs {BASELINE['mean_rho']:.6f} (error: {error_mean_rho:.6f})")
        all_passed = False
    
    # Verifica mean_K
    error_mean_K = abs(mean_K - BASELINE['mean_K'])
    if error_mean_K <= BASELINE['tolerance_mean']:
        print(f"   ✓ Mean K: {mean_K:.6f} (baseline: {BASELINE['mean_K']:.6f}, error: {error_mean_K:.6f})")
    else:
        print(f"   ❌ Mean K cambiato: {mean_K:.6f} vs {BASELINE['mean_K']:.6f} (error: {error_mean_K:.6f})")
        all_passed = False
    
    # Verifica range rho
    error_min_rho = abs(min_rho - BASELINE['min_rho'])
    error_max_rho = abs(max_rho - BASELINE['max_rho'])
    if error_min_rho <= BASELINE['tolerance_range'] and error_max_rho <= BASELINE['tolerance_range']:
        print(f"   ✓ Range ρ: [{min_rho:.6f}, {max_rho:.6f}] (baseline: [{BASELINE['min_rho']:.6f}, {BASELINE['max_rho']:.6f}])")
    else:
        print(f"   ⚠ Range ρ cambiato: [{min_rho:.6f}, {max_rho:.6f}] vs [{BASELINE['min_rho']:.6f}, {BASELINE['max_rho']:.6f}]")
        # Non fallisce, solo warning
    
    # Verifica numero di computazioni
    if len(results) == BASELINE['n_computations']:
        print(f"   ✓ Numero di computazioni: {len(results)} (baseline: {BASELINE['n_computations']})")
    else:
        print(f"   ⚠ Numero di computazioni cambiato: {len(results)} vs {BASELINE['n_computations']}")
        # Non fallisce, solo warning
    
    return all_passed

def regression_test_structure(results):
    """Verifica che la struttura dei risultati sia consistente"""
    print("\n2. Test di regressione: Struttura dati")
    print("-" * 70)
    
    all_passed = True
    
    # Verifica che ogni risultato abbia i campi necessari
    required_fields = ['curve', 'prime', 'rho', 'K', 'cov', 'var_11', 'var_22', 
                      'errors_11', 'errors_22']
    
    for i, r in enumerate(results):
        missing_fields = [f for f in required_fields if f not in r]
        if missing_fields:
            print(f"   ❌ Risultato {i} manca campi: {missing_fields}")
            all_passed = False
        else:
            # Verifica che errors_11 e errors_22 abbiano la stessa lunghezza
            if len(r['errors_11']) != len(r['errors_22']):
                print(f"   ❌ Risultato {i}: lunghezze errori diverse")
                all_passed = False
    
    if all_passed:
        print(f"   ✓ Tutti i {len(results)} risultati hanno struttura corretta")
    
    return all_passed

def regression_test_formulas(results):
    """Verifica che le formule siano ancora corrette"""
    print("\n3. Test di regressione: Formule")
    print("-" * 70)
    
    all_passed = True
    
    for r in results:
        rho = r['rho']
        K_computed = r['K']
        K_theoretical = 4.0 / (1.0 + rho)**2
        
        if abs(K_computed - K_theoretical) > 1e-5:
            print(f"   ❌ Formula K errata per ρ = {rho:.6f}")
            all_passed = False
    
    if all_passed:
        print(f"   ✓ Tutte le formule K sono corrette")
    
    return all_passed

def main():
    """Esegue tutti i test di regressione"""
    print("=" * 70)
    print("TEST DI REGRESSIONE")
    print("=" * 70)
    print(f"\nBaseline:")
    print(f"  Mean ρ: {BASELINE['mean_rho']:.6f}")
    print(f"  Mean K: {BASELINE['mean_K']:.6f}")
    print(f"  Range ρ: [{BASELINE['min_rho']:.6f}, {BASELINE['max_rho']:.6f}]")
    print(f"  N computations: {BASELINE['n_computations']}")
    
    results = load_results()
    if results is None:
        return False
    
    print(f"\nRisultati attuali: {len(results)} computazioni")
    
    all_passed = True
    
    all_passed &= regression_test_statistics(results)
    all_passed &= regression_test_structure(results)
    all_passed &= regression_test_formulas(results)
    
    print("\n" + "=" * 70)
    if all_passed:
        print("✓ TUTTI I TEST DI REGRESSIONE PASSATI!")
    else:
        print("❌ ALCUNI TEST FALLITI")
    print("=" * 70)
    
    return all_passed

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
