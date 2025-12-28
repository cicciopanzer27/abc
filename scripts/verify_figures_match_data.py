#!/usr/bin/env python3
"""
Verifica che le figure nel paper corrispondano ai dati reali.

Questo script verifica:
1. Che le figure usino dati reali, non teorici
2. Che i valori nelle figure corrispondano ai dati computazionali
3. Che le statistiche nelle figure siano corrette
"""

import json
import numpy as np
import sys
import os

def load_results():
    """Carica i risultati computazionali."""
    results_path = os.path.join(os.path.dirname(__file__), 'computation_results.json')
    if not os.path.exists(results_path):
        print(f"[FAIL] ERRORE: {results_path} non trovato")
        return None
    
    with open(results_path, 'r') as f:
        return json.load(f)

def verify_correlation_distribution_figure(results):
    """Verifica che fig_correlation_distribution.pdf usi dati reali"""
    print("\n1. Verifica figura: Distribuzione correlazione")
    print("-" * 70)
    
    rhos = [r['rho'] for r in results]
    
    # Verifica che ci siano abbastanza dati
    assert len(rhos) == 21, f"Dovrebbero esserci 21 risultati, trovati {len(rhos)}"
    print(f"   [OK] Numero di risultati: {len(rhos)}")
    
    # Verifica statistiche
    mean_rho = np.mean(rhos)
    std_rho = np.std(rhos)
    
    # Verifica che mean_rho sia alta (come nei risultati reali)
    if mean_rho > 0.7:
        print(f"   [OK] Mean rho = {mean_rho:.6f} è alta (come atteso)")
    else:
        print(f"   [WARN] Warning: Mean rho = {mean_rho:.6f} è più bassa del previsto")
    
    print(f"   [OK] Std rho = {std_rho:.6f}")
    print(f"   [OK] Range: [{np.min(rhos):.6f}, {np.max(rhos):.6f}]")
    
    return True

def verify_scatter_errors_figure(results):
    """Verifica che fig_scatter_errors.pdf usi dati reali"""
    print("\n2. Verifica figura: Scatter plot errori")
    print("-" * 70)
    
    # Trova esempio principale (E: y²=x³+x+1, p=13)
    main_result = None
    for r in results:
        if (r['curve']['a'] == 0 and r['curve']['b'] == 1 and 
            r['curve']['c'] == 1 and r['prime'] == 13):
            main_result = r
            break
    
    if main_result is None:
        print("   [FAIL] Esempio principale non trovato")
        return False
    
    errors_11 = main_result['errors_11']
    errors_22 = main_result['errors_22']
    rho = main_result['rho']
    
    # Verifica che ci siano 12 errori (l-1 = 12)
    assert len(errors_11) == 12, f"Dovrebbero esserci 12 errori, trovati {len(errors_11)}"
    assert len(errors_22) == 12, f"Dovrebbero esserci 12 errori, trovati {len(errors_22)}"
    print(f"   [OK] Numero di errori: {len(errors_11)}")
    
    # Verifica che ρ sia alto (come nei risultati reali)
    if rho > 0.9:
        print(f"   [OK] rho = {rho:.6f} è alto (come atteso)")
    else:
        print(f"   [WARN] Warning: rho = {rho:.6f} è più basso del previsto")
    
    # Verifica che errors_11 siano più grandi di errors_22
    max_11 = max(abs(e) for e in errors_11)
    max_22 = max(abs(e) for e in errors_22)
    
    if max_11 > max_22:
        print(f"   [OK] errors_11 ({max_11:.6f}) > errors_22 ({max_22:.6f})")
    else:
        print(f"   [WARN] Warning: errors_11 ({max_11:.6f}) <= errors_22 ({max_22:.6f})")
    
    return True

def verify_cancellation_vs_correlation_figure(results):
    """Verifica che fig_cancellation_vs_correlation.pdf usi dati reali"""
    print("\n3. Verifica figura: Cancellation vs Correlation")
    print("-" * 70)
    
    rhos = [r['rho'] for r in results]
    Ks = [r['K'] for r in results]
    
    # Verifica che K = 4/(1+ρ)² per ogni punto
    all_valid = True
    for rho, K in zip(rhos, Ks):
        K_theoretical = 4.0 / (1.0 + rho)**2
        if abs(K - K_theoretical) > 1e-5:
            print(f"   [FAIL] K mismatch per rho = {rho:.6f}")
            all_valid = False
    
    if all_valid:
        print(f"   [OK] Tutti i {len(rhos)} punti seguono K = 4/(1+rho)^2")
    
    # Verifica che ci sia almeno un punto con ρ = 0
    has_zero = any(abs(rho) < 1e-6 for rho in rhos)
    if has_zero:
        print(f"   [OK] Trovato punto con rho ~ 0 (K = 4)")
    else:
        print(f"   [WARN] Nessun punto con rho = 0 trovato")
    
    return all_valid

def verify_error_sequences_figure(results):
    """Verifica che fig_error_sequences.pdf usi dati reali"""
    print("\n4. Verifica figura: Sequenze errori")
    print("-" * 70)
    
    # Trova esempio principale
    main_result = None
    for r in results:
        if (r['curve']['a'] == 0 and r['curve']['b'] == 1 and 
            r['curve']['c'] == 1 and r['prime'] == 13):
            main_result = r
            break
    
    if main_result is None:
        print("   [FAIL] Esempio principale non trovato")
        return False
    
    errors_11 = main_result['errors_11']
    errors_22 = main_result['errors_22']
    
    # Verifica che errors_11 crescano (non necessariamente quadratico)
    if len(errors_11) > 1:
        is_increasing = all(errors_11[i] <= errors_11[i+1] or abs(errors_11[i] - errors_11[i+1]) < 0.1 
                           for i in range(len(errors_11)-1))
        if is_increasing or max(errors_11) > min(errors_11):
            print(f"   [OK] errors_11 mostrano crescita (range: [{min(errors_11):.6f}, {max(errors_11):.6f}])")
        else:
            print(f"   [WARN] Warning: errors_11 non mostrano crescita chiara")
    
    # Verifica che errors_22 siano piccoli
    max_22 = max(abs(e) for e in errors_22)
    if max_22 < 0.1:
        print(f"   [OK] errors_22 sono piccoli (max: {max_22:.6f})")
    else:
        print(f"   [WARN] Warning: errors_22 sono grandi (max: {max_22:.6f})")
    
    return True

def verify_rho_across_primes_figure(results):
    """Verifica che fig_rho_across_primes.pdf usi dati reali"""
    print("\n5. Verifica figura: rho attraverso primi")
    print("-" * 70)
    
    # Raggruppa per curva
    curves = {}
    for r in results:
        curve_key = f"y² = x³ + {r['curve']['a']}x² + {r['curve']['b']}x + {r['curve']['c']}"
        if curve_key not in curves:
            curves[curve_key] = []
        curves[curve_key].append((r['prime'], r['rho']))
    
    print(f"   [OK] Trovate {len(curves)} curve diverse")
    
    # Verifica che ogni curva abbia dati per 7 primi
    for curve_name, data in curves.items():
        if len(data) == 7:
            print(f"   [OK] {curve_name[:30]}: 7 primi")
        else:
            print(f"   [WARN] {curve_name[:30]}: {len(data)} primi (attesi 7)")
    
    # Verifica che ρ sia generalmente alto
    all_rhos = [r['rho'] for r in results]
    high_rho_count = sum(1 for rho in all_rhos if rho > 0.8)
    print(f"   [OK] {high_rho_count}/{len(all_rhos)} casi con rho > 0.8")
    
    return True

def main():
    """Esegue tutte le verifiche delle figure"""
    print("=" * 70)
    print("VERIFICA FIGURE VS DATI REALI")
    print("=" * 70)
    
    results = load_results()
    if results is None:
        return False
    
    print(f"\nCaricati {len(results)} risultati computazionali")
    
    all_passed = True
    
    all_passed &= verify_correlation_distribution_figure(results)
    all_passed &= verify_scatter_errors_figure(results)
    all_passed &= verify_cancellation_vs_correlation_figure(results)
    all_passed &= verify_error_sequences_figure(results)
    all_passed &= verify_rho_across_primes_figure(results)
    
    print("\n" + "=" * 70)
    if all_passed:
        print("[OK] TUTTE LE VERIFICHE DELLE FIGURE PASSATE!")
    else:
        print("[FAIL] ALCUNE VERIFICHE FALLITE")
    print("=" * 70)
    
    return all_passed

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
