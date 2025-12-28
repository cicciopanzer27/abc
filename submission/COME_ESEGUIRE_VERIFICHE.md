# Come Eseguire le Verifiche

## ⚠️ IMPORTANTE: Directory Corretta

Gli script di verifica sono nella directory:
```
C:\Users\jecho\Documents\GitHub\abc\scripts\
```

**NON** in `C:\Users\jecho\Desktop\qt\abc\scripts\`

## Esecuzione

### 1. Verifica Completa (Tutte le Verifiche)

```powershell
cd C:\Users\jecho\Documents\GitHub\abc
python scripts/verify_all_fixed.py
```

### 2. Verifiche Individuali

```powershell
cd C:\Users\jecho\Documents\GitHub\abc

# Consistenza teoria-calcoli
python scripts/verify_theory_computation_consistency.py

# Figure vs dati reali
python scripts/verify_figures_match_data.py

# Test di regressione
python scripts/regression_tests.py

# Verifica correlazione
python scripts/verify_correlation.py

# Verifica figure teoriche
python scripts/verify_figures.py
```

## Verifiche Disponibili

1. **verify_theory_computation_consistency.py**
   - Verifica range teorico di rho: [-1, 1]
   - Verifica formula K = 4/(1+rho)^2
   - Verifica scaling degli errori
   - Verifica statistiche
   - Verifica calcolo covarianza

2. **verify_figures_match_data.py**
   - Verifica che le figure usino dati reali
   - Verifica scatter plot errori
   - Verifica cancellation vs correlation
   - Verifica sequenze errori
   - Verifica rho attraverso primi

3. **regression_tests.py**
   - Test di regressione contro baseline
   - Verifica struttura dati
   - Verifica formule

4. **verify_correlation.py**
   - Verifica correlazione per multiple curve/primi

5. **verify_figures.py**
   - Verifica figure teoriche
   - Verifica scaling O(sqrt(eps)) vs O(eps)
   - Verifica accumulazione errori
   - Verifica ottimizzazione parametri
   - Verifica analisi correlazione
   - Verifica estensioni dimensioni superiori

## Risultati Attesi

Tutte le verifiche dovrebbero passare con:
- `[OK]` per ogni verifica superata
- `[FAIL]` per errori
- `[WARN]` per warning

## Troubleshooting

### Errore: "can't open file"
- **Causa**: Stai eseguendo dalla directory sbagliata
- **Soluzione**: Usa `cd C:\Users\jecho\Documents\GitHub\abc` prima di eseguire

### Errore: "computation_results.json non trovato"
- **Causa**: I calcoli reali non sono stati eseguiti
- **Soluzione**: Esegui prima `python scripts/run_complete_computations.py`

### Errore Unicode
- **Causa**: Problemi di encoding su Windows
- **Soluzione**: Gli script sono già corretti per evitare questi errori
