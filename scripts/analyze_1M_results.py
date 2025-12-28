"""Analyze 1M simulations results"""
import json
import numpy as np

# Load results
with open('1M_simulations_results.json', 'r') as f:
    data = json.load(f)

print("=" * 80)
print("1M SIMULATIONS RESULTS ANALYSIS")
print("=" * 80)
print(f"Total simulations: {data['total_simulations']}")
print(f"Successful: {data['successful']}")
print(f"Failed: {data['failed']}")
print(f"Success rate: {data['success_rate']:.2f}%")
print()

results = data['results']
rhos = [r['rho'] for r in results]
Ks = [r['K'] for r in results]

print("Correlation (rho):")
print(f"  Mean:   {np.mean(rhos):.9f}")
print(f"  Std:    {np.std(rhos):.9f}")
print(f"  Min:    {np.min(rhos):.9f}")
print(f"  Max:    {np.max(rhos):.9f}")
print(f"  Median: {np.median(rhos):.9f}")

# 95% confidence interval for rho
std_error_rho = np.std(rhos) / np.sqrt(len(rhos))
ci_lower_rho = np.mean(rhos) - 1.96 * std_error_rho
ci_upper_rho = np.mean(rhos) + 1.96 * std_error_rho
ci_width_rho = ci_upper_rho - ci_lower_rho
print(f"  95% CI: [{ci_lower_rho:.9f}, {ci_upper_rho:.9f}]")
print(f"  CI width: {ci_width_rho:.9f} ({ci_width_rho/np.mean(rhos)*100:.6f}% of mean)")

print()
print("Cancellation Constant (K):")
print(f"  Mean:   {np.mean(Ks):.9f}")
print(f"  Std:    {np.std(Ks):.9f}")
print(f"  Min:    {np.min(Ks):.9f}")
print(f"  Max:    {np.max(Ks):.9f}")
print(f"  Median: {np.median(Ks):.9f}")

# 95% confidence interval for K
std_error_K = np.std(Ks) / np.sqrt(len(Ks))
ci_lower_K = np.mean(Ks) - 1.96 * std_error_K
ci_upper_K = np.mean(Ks) + 1.96 * std_error_K
ci_width_K = ci_upper_K - ci_lower_K
print(f"  95% CI: [{ci_lower_K:.9f}, {ci_upper_K:.9f}]")
print(f"  CI width: {ci_width_K:.9f}")

print()
print("Distribution:")
high_corr = sum(1 for r in rhos if r > 0.8)
medium_corr = sum(1 for r in rhos if 0.3 <= r <= 0.8)
low_corr = sum(1 for r in rhos if 0 <= r < 0.3)
zero_corr = sum(1 for r in rhos if abs(r) < 0.01)

print(f"  High correlation (rho > 0.8): {high_corr}/{len(results)} ({100*high_corr/len(results):.2f}%)")
print(f"  Medium correlation (0.3 <= rho <= 0.8): {medium_corr}/{len(results)} ({100*medium_corr/len(results):.2f}%)")
print(f"  Low correlation (0 <= rho < 0.3): {low_corr}/{len(results)} ({100*low_corr/len(results):.2f}%)")
print(f"  Near-zero correlation (|rho| < 0.01): {zero_corr}/{len(results)} ({100*zero_corr/len(results):.2f}%)")

print()
print("Framework Validity:")
K_valid = sum(1 for k in Ks if k >= 1.0)
print(f"  K >= 1: {K_valid}/{len(results)} ({100*K_valid/len(results):.2f}%)")

print("=" * 80)
