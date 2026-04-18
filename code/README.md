# ZHY Covariance Estimator

Implementation of the optimal weighted Zhou-Hayashi-Yoshida (ZHY) covariance
estimator with exact finite-sample conditional variance and precision-weighted
shrinkage for multi-asset covariance matrix estimation.

## Background

Based on the DPhil thesis:

> Yang Wu Azzollini (2016). *High-Frequency Covariance Estimation*.
> DPhil Thesis, University of Oxford.
> Supervised by Professor Brian D. Ripley and Dr Peter Clifford.

**Theorem 1 (Chapter 5):** For the general weighted ZHY estimator
with weights {w_ij}, the exact finite-sample conditional variance is:

    Var(sigma_hat_12 | tau) = sigma_1^2 * sigma_2^2 * A1 + sigma_12^2 * A2

where A1 and A2 are explicit functions of the overlap structure {tau_ij},
the interval lengths {tau_i^X, tau_j^Y}, and the weights {w_ij}.

This result is **exact** (not asymptotic), **model-free** (no distributional
assumption on observation times), and holds for any fixed set of timestamps.

**Optimal weights** minimising A1 via Lagrange multiplier:

    w_ij* = tau_ij / (tau_i^X * tau_j^Y)

## Files

| File | Description |
|------|-------------|
| `zhy_estimator.py` | Core estimator: pairwise ZHY, exact variance, multi-asset matrix |
| `crypto_demo.py`   | Demo on five crypto assets (BTC, ETH, SOL, LINK, ADA) |
| `plot_results.py`  | Six-panel comparison figure |

## Quick Start

```bash
# Run demo (simulated data)
python crypto_demo.py

# Generate figure
python plot_results.py
```

## Key Results (simulated, one trading day)

| Method                        | Frobenius Error | vs Naive |
|-------------------------------|-----------------|----------|
| Naive 5-min synchronised      | 0.2601          | 1.0x     |
| Optimal ZHY (Theorem 1)       | 0.0676          | **3.8x better** |
| Precision-weighted shrinkage  | 0.0674          | **3.9x better** |

The precision matrix shows BTC/ETH is estimated with 1000x higher
precision than LINK/ADA, correctly reflecting the difference in
trade rates (50 vs 3 trades/minute).

## Using Real Data

Replace `simulate_tick_data()` in `crypto_demo.py` with:

```python
import requests, pandas as pd

def load_binance_data(symbol='BTCUSDT', date='2024-01-15'):
    """Load tick data from Binance historical data portal."""
    # Free data: https://data.binance.vision
    url = f'https://data.binance.vision/data/spot/daily/trades/{symbol}/{symbol}-trades-{date}.zip'
    df = pd.read_csv(url, names=['id','price','qty','qbase','time','buyer','maker','ignore'])
    df['time_min'] = df['time'] / 60000.0   # ms -> minutes
    df['log_price'] = np.log(df['price'].astype(float))
    return df[['time_min', 'log_price']].reset_index(drop=True)
```

## Repository

GitHub: https://github.com/ChubbyFaceEuler/Paper_2026

## Citation

If you use this code, please cite:

```
Yang Wu Azzollini (2016). High-Frequency Covariance Estimation.
DPhil Thesis, University of Oxford.
```
