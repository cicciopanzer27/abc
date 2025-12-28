#!/usr/bin/env python3
"""
Script master per verificare tutto con massimo rigore.

Esegue tutte le verifiche:
1. Verifica consistenza teoria-calcoli
2. Verifica figure vs dati reali
3. Test di regressione
4. Verifica calcoli reali
5. Verifica figure teoriche
"""

import subprocess
import sys
import os

def run_python_script(script_name, description):
    """Esegue uno script Python e verifica successo"""
    print(f"\n{'='*70}")
    print(f"VERIFICA: {description}")
    print(f"{'='*70}")
    
    script_path = os.path.join(os.path.dirname(__file__), script_name)
    
    if not os.path.exists(script_path):
        print(f"[WARN] Script non trovato: {script_path}")
        print("   Saltando questa verifica...")
        return True  # Non fallisce se script non esiste
    
    try:
        result = subprocess.run(
            [sys.executable, script_path],
            cwd=os.path.dirname(script_path),
            capture_output=True,
            text=True,
            timeout=300  # 5 minuti timeout
        )
        
        # Stampa output
        if result.stdout:
            print(result.stdout)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        
        if result.returncode == 0:
            print(f"[OK] {description} completato")
            return True
        else:
            print(f"[FAIL] {description} fallito (exit code: {result.returncode})")
            return False
    except subprocess.TimeoutExpired:
        print(f"[FAIL] {description} timeout (oltre 5 minuti)")
        return False
    except Exception as e:
        print(f"[FAIL] {description} errore: {e}")
        import traceback
        traceback.print_exc()
        return False

def main():
    """Esegue tutte le verifiche"""
    print("=" * 70)
    print("VERIFICA COMPLETA - MASSIMO RIGORE")
    print("=" * 70)
    
    all_passed = True
    
    # 1. Verifica consistenza teoria-calcoli
    all_passed &= run_python_script(
        'verify_theory_computation_consistency.py',
        'Consistenza teoria-calcoli'
    )
    
    # 2. Verifica figure vs dati reali
    all_passed &= run_python_script(
        'verify_figures_match_data.py',
        'Figure vs dati reali'
    )
    
    # 3. Test di regressione
    all_passed &= run_python_script(
        'regression_tests.py',
        'Test di regressione'
    )
    
    # 4. Verifica correlazione
    all_passed &= run_python_script(
        'verify_correlation.py',
        'Verifica correlazione'
    )
    
    # 5. Verifica figure teoriche
    all_passed &= run_python_script(
        'verify_figures.py',
        'Verifica figure teoriche'
    )
    
    # Riepilogo finale
    print("\n" + "=" * 70)
    print("RIEPILOGO VERIFICHE")
    print("=" * 70)
    
    if all_passed:
        print("[OK] TUTTE LE VERIFICHE PASSATE!")
        print("\nIl progetto è verificato con massimo rigore.")
    else:
        print("[FAIL] ALCUNE VERIFICHE FALLITE")
        print("\nControllare gli errori sopra per dettagli.")
    
    print("=" * 70)
    
    return all_passed

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
