"""
Crypto Demo: Precision-Weighted ZHY Covariance Estimation
==========================================================
Demonstrates the optimal weighted ZHY estimator on five crypto assets
spanning a range of liquidity.

Assets:
    BTC  - 50 trades/min  (most liquid)
    ETH  - 35 trades/min
    SOL  - 15 trades/min
    LINK -  5 trades/min
    ADA  -  3 trades/min  (least liquid)

Results:
    Naive 5-min synchronised:          Frobenius error 0.2601
    Optimal ZHY (Theorem 1 weights):   Frobenius error 0.0676  (3.8x better)
    Precision-weighted shrinkage:      Frobenius error 0.0674

The precision matrix (from the exact variance formula) shows BTC/ETH
is estimated 1000x more precisely than LINK/ADA, correctly reflecting
the difference in trade rates and overlap structure.

To run on real data:
    Replace simulate_tick_data() with load_binance_data() below.
    Binance historical data: https://data.binance.vision
"""

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import pickle
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))
from zhy_estimator import build_covariance_matrix, frobenius_error

# ============================================================
# Parameters
# ============================================================
COINS = {
    'BTC':  {'rate': 50.0,  'sigma': 0.000219},
    'ETH':  {'rate': 35.0,  'sigma': 0.000293},
    'SOL':  {'rate': 15.0,  'sigma': 0.000438},
    'LINK': {'rate':  5.0,  'sigma': 0.000663},
    'ADA':  {'rate':  3.0,  'sigma': 0.000791},
}
names = list(COINS.keys())
n = len(names)

RHO_TRUE = np.array([
    [1.00, 0.85, 0.65, 0.50, 0.45],
    [0.85, 1.00, 0.70, 0.55, 0.48],
    [0.65, 0.70, 1.00, 0.60, 0.52],
    [0.50, 0.55, 0.60, 1.00, 0.58],
    [0.45, 0.48, 0.52, 0.58, 1.00],
])

sigmas = np.array([COINS[c]['sigma'] for c in names])
SIGMA_TRUE = np.outer(sigmas, sigmas) * RHO_TRUE


# ============================================================
# Simulate tick data (replace with real data loader)
# ============================================================
def simulate_tick_data(T_min=1440.0, seed=2024):
    """
    Simulate one day of correlated crypto tick data.

    Replace this function with load_binance_data() for real data.
    """
    np.random.seed(seed)
    L = np.linalg.cholesky(SIGMA_TRUE)
    dt_fine = 0.1
    n_fine = int(T_min / dt_fine)
    Z = np.random.randn(n_fine, n)
    dW = (Z @ L.T) * np.sqrt(dt_fine)
    log_prices_fine = np.cumsum(dW, axis=0)
    t_fine = np.arange(1, n_fine + 1) * dt_fine

    tick_data = {}
    for k, (coin, params) in enumerate(COINS.items()):
        n_trades = np.random.poisson(params['rate'] * T_min)
        n_trades = max(n_trades, 10)
        trade_times = np.sort(np.random.uniform(0, T_min, n_trades))
        idx = np.searchsorted(t_fine, trade_times, 'right') - 1
        idx = np.clip(idx, 0, n_fine - 1)
        tick_data[coin] = pd.DataFrame({
            'time_min':  trade_times,
            'log_price': log_prices_fine[idx, k]
        })
    return tick_data


def naive_5min_corr(tick_data, window_min=5.0):
    """Previous-tick synchronisation, standard sample correlation."""
    T_end   = min(tick_data[c]['time_min'].iloc[-1] for c in names)
    T_start = max(tick_data[c]['time_min'].iloc[0]  for c in names)
    grid = np.arange(T_start, T_end, window_min)
    synced = {}
    for coin in names:
        df = tick_data[coin]
        t = df['time_min'].values
        p = df['log_price'].values
        idx = np.searchsorted(t, grid, 'right') - 1
        idx = np.clip(idx, 0, len(p) - 1)
        synced[coin] = p[idx]
    ret_mat = np.column_stack([np.diff(synced[c]) for c in names])
    cov = np.cov(ret_mat.T)
    std = np.sqrt(np.diag(cov))
    return cov / np.outer(std, std)


# ============================================================
# Main
# ============================================================
if __name__ == '__main__':
    print("Simulating tick data...")
    tick_data = simulate_tick_data()
    for c, df in tick_data.items():
        avg_sec = 1440.0 / len(df) * 60
        print(f"  {c}: {len(df):,} trades  (avg {avg_sec:.1f}s between trades)")

    print("\nBuilding ZHY covariance matrix...")
    out = build_covariance_matrix(tick_data, window_min=60.0)

    print("\nBuilding naive 5-min matrix...")
    RHO_NAIVE = naive_5min_corr(tick_data)

    # Errors
    err_naive  = frobenius_error(RHO_NAIVE,          RHO_TRUE)
    err_zhy    = frobenius_error(out['RHO_ZHY'],     RHO_TRUE)
    err_shrunk = frobenius_error(out['RHO_SHRUNK'],  RHO_TRUE)

    print(f"\nFrobenius errors vs true correlation:")
    print(f"  Naive 5-min:              {err_naive:.4f}")
    print(f"  Optimal ZHY (Theorem 1):  {err_zhy:.4f}  "
          f"({err_naive/err_zhy:.1f}x better)")
    print(f"  Precision-weighted shrunk:{err_shrunk:.4f}  "
          f"({err_naive/err_shrunk:.1f}x better)")

    print(f"\nPair-by-pair results:")
    print(f"{'Pair':<12} {'rho_true':>9} {'rho_est':>9} "
          f"{'error':>8} {'log10(prec)':>12}")
    print("-" * 55)
    for (c1, c2), res in out['pair_results'].items():
        ki = names.index(c1); kj = names.index(c2)
        rho_t = RHO_TRUE[ki, kj]
        rho_e = res['rho_est']
        prec  = res['precision']
        print(f"  {c1}/{c2:<8} {rho_t:>9.3f} {rho_e:>9.3f} "
              f"{abs(rho_e - rho_t):>8.4f} "
              f"{np.log10(prec) if prec > 0 else 0:>12.1f}")

    print("\nSaving results...")
    np.save('/tmp/RHO_ZHY.npy',    out['RHO_ZHY'])
    np.save('/tmp/RHO_SHRUNK.npy', out['RHO_SHRUNK'])
    np.save('/tmp/RHO_NAIVE.npy',  RHO_NAIVE)
    np.save('/tmp/PRECISION.npy',  out['PRECISION'])
    np.save('/tmp/RHO_TRUE.npy',   RHO_TRUE)
    print("Done. Run plot_results.py to generate figures.")
