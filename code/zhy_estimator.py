"""
ZHY Covariance Estimator
========================
Implementation of the optimal weighted Zhou-Hayashi-Yoshida covariance
estimator with exact finite-sample variance, precision-weighted shrinkage,
and multi-asset covariance matrix construction.

Based on:
    Yang Wu Azzollini, DPhil Thesis, University of Oxford, 2016
    Supervised by Professor Brian D. Ripley and Dr Peter Clifford

    Theorem 1 (Chapter 5):
        Var(sigma_hat | tau) = sigma1^2 * sigma2^2 * A1 + sigma12^2 * A2

        where A1 and A2 are explicit functions of the overlap structure
        {tau_ij}, the interval lengths {tau_i^X}, {tau_j^Y}, and the
        weights {w_ij}. This result is exact, finite-sample, and model-free.

    Optimal weights (Chapter 5, Section 4):
        w_ij = tau_ij / (tau_i^X * tau_j^Y)

        These minimise A1 in Var(sigma_hat | tau) by a Lagrange multiplier
        argument. The resulting estimator dominates the basic HY estimator
        in terms of the coefficient of sigma1^2 * sigma2^2.

Usage:
    See demo at bottom of file, or crypto_demo.py for full pipeline.

Author: Yang Wu Azzollini (implementation by Claude, April 2026)
"""

import numpy as np
import pandas as pd
from typing import Dict, List, Tuple, Optional


# ============================================================
# Core pairwise estimator
# ============================================================

def compute_overlaps_windowed(
        times_x: np.ndarray,
        times_y: np.ndarray,
        returns_x: np.ndarray,
        returns_y: np.ndarray
) -> Tuple[float, float, float, float, int]:
    """
    Compute the ZHY numerator, T(w), A1_numerator, A2_numerator
    for one window of observations.

    Uses optimal weights w_ij = tau_ij / (tau_i^X * tau_j^Y).

    Parameters
    ----------
    times_x  : observation times for asset X (including t_0)
    times_y  : observation times for asset Y (including u_0)
    returns_x: log-price differences for X (length m = len(times_x) - 1)
    returns_y: log-price differences for Y (length n = len(times_y) - 1)

    Returns
    -------
    numerator  : sum_ij R_i S_j w_ij I(tau_ij > 0)
    T_w        : sum_ij tau_ij w_ij  (normalisation)
    A1_num     : sum_ij w_ij^2 tau_i^X tau_j^Y  (A1 numerator)
    A2_num     : row/col sum term for A2
    n_overlaps : number of overlapping pairs
    """
    lx = times_x[:-1];  rx = times_x[1:]
    ly = times_y[:-1];  ry = times_y[1:]
    tau_x = rx - lx
    tau_y = ry - ly
    m = len(lx)
    n_y = len(ly)

    # Build overlap matrix (full, for small windows)
    # For large windows use the windowed approach in estimate_pair_windowed
    numerator  = 0.0
    T_w        = 0.0
    A1_num     = 0.0
    n_overlaps = 0

    # For A2 we need row and col sums of w_ij * tau_ij
    row_w_tau = np.zeros(m)
    col_w_tau = np.zeros(n_y)
    w_sq_tau_sq = 0.0

    for i in range(m):
        for j in range(n_y):
            tau_ij = max(0.0,
                         min(rx[i], ry[j]) - max(lx[i], ly[j]))
            if tau_ij > 1e-12:
                denom = tau_x[i] * tau_y[j]
                if denom > 1e-20:
                    w_ij = tau_ij / denom
                    numerator  += returns_x[i] * returns_y[j] * w_ij
                    T_w        += tau_ij * w_ij
                    A1_num     += w_ij**2 * tau_x[i] * tau_y[j]
                    row_w_tau[i] += w_ij * tau_ij
                    col_w_tau[j] += w_ij * tau_ij
                    w_sq_tau_sq  += w_ij**2 * tau_ij**2
                    n_overlaps   += 1

    A2_num = (np.sum(row_w_tau**2) + np.sum(col_w_tau**2)
              - w_sq_tau_sq)

    return numerator, T_w, A1_num, A2_num, n_overlaps


def estimate_pair(
        df_x: pd.DataFrame,
        df_y: pd.DataFrame,
        sigma1_sq: Optional[float] = None,
        sigma2_sq: Optional[float] = None,
        window_min: float = 60.0,
        time_col: str = 'time_min',
        price_col: str = 'log_price'
) -> Dict:
    """
    Estimate covariance between two assets using the optimal weighted
    ZHY estimator with exact conditional variance (Theorem 1).

    Processes data in non-overlapping windows of length window_min
    to avoid memory issues with large datasets.

    Parameters
    ----------
    df_x, df_y   : DataFrames with columns [time_col, price_col]
    sigma1_sq    : variance of asset X (estimated if None)
    sigma2_sq    : variance of asset Y (estimated if None)
    window_min   : window length in same units as time_col
    time_col     : column name for observation times
    price_col    : column name for log-prices

    Returns
    -------
    dict with keys:
        sigma_opt  : optimal weighted ZHY estimate of covariance
        rho_est    : estimated correlation
        variance   : exact conditional variance from Theorem 1
        A1, A2     : variance components
        precision  : 1 / variance
        n_overlaps : total overlapping pairs used
        T_w        : normalisation constant
    """
    T_start = max(df_x[time_col].iloc[0],  df_y[time_col].iloc[0])
    T_end   = min(df_x[time_col].iloc[-1], df_y[time_col].iloc[-1])

    # Per-asset variance if not supplied
    if sigma1_sq is None:
        T1 = df_x[time_col].iloc[-1] - df_x[time_col].iloc[0]
        ret1 = np.diff(df_x[price_col].values)
        sigma1_sq = float(np.sum(ret1**2) / T1)
    if sigma2_sq is None:
        T2 = df_y[time_col].iloc[-1] - df_y[time_col].iloc[0]
        ret2 = np.diff(df_y[price_col].values)
        sigma2_sq = float(np.sum(ret2**2) / T2)

    # Aggregate over windows
    total_num  = 0.0
    total_T_w  = 0.0
    total_A1_n = 0.0
    total_A2_n = 0.0
    total_over = 0

    windows = np.arange(T_start, T_end, window_min)
    for w_start in windows:
        w_end = w_start + window_min

        mx = ((df_x[time_col] >= w_start) &
              (df_x[time_col] <= w_end))
        my = ((df_y[time_col] >= w_start) &
              (df_y[time_col] <= w_end))

        tx = df_x.loc[mx, time_col].values
        ty = df_y.loc[my, time_col].values
        px = df_x.loc[mx, price_col].values
        py = df_y.loc[my, price_col].values

        if len(tx) < 2 or len(ty) < 2:
            continue

        rx_w = np.diff(px)
        ry_w = np.diff(py)

        num, T_w, A1_n, A2_n, n_ov = compute_overlaps_windowed(
            tx, ty, rx_w, ry_w)

        total_num  += num
        total_T_w  += T_w
        total_A1_n += A1_n
        total_A2_n += A2_n
        total_over += n_ov

    if total_T_w == 0:
        return None

    sigma_opt = total_num / total_T_w
    T_w_sq = total_T_w**2

    # --- Exact variance: Theorem 1 ---
    A1 = total_A1_n / T_w_sq
    A2 = total_A2_n / T_w_sq

    sigma12_sq = sigma_opt**2
    variance   = sigma1_sq * sigma2_sq * A1 + sigma12_sq * A2
    precision  = 1.0 / variance if variance > 0 else 0.0
    rho_est    = (sigma_opt / np.sqrt(sigma1_sq * sigma2_sq)
                  if sigma1_sq > 0 and sigma2_sq > 0 else 0.0)

    return {
        'sigma_opt':   sigma_opt,
        'rho_est':     rho_est,
        'variance':    variance,
        'A1':          A1,
        'A2':          A2,
        'precision':   precision,
        'n_overlaps':  total_over,
        'T_w':         total_T_w,
        'sigma1_sq':   sigma1_sq,
        'sigma2_sq':   sigma2_sq,
    }


# ============================================================
# Multi-asset covariance matrix
# ============================================================

def build_covariance_matrix(
        tick_data: Dict[str, pd.DataFrame],
        window_min: float = 60.0,
        time_col: str = 'time_min',
        price_col: str = 'log_price'
) -> Dict:
    """
    Build the full p x p covariance and correlation matrices using
    pairwise optimal ZHY estimates with exact conditional variance.

    Parameters
    ----------
    tick_data : dict mapping coin name -> DataFrame
    window_min: window length for ZHY computation
    time_col  : column for observation times
    price_col : column for log-prices

    Returns
    -------
    dict with:
        names       : list of asset names
        RHO_ZHY     : p x p correlation matrix (optimal ZHY)
        RHO_SHRUNK  : p x p precision-weighted shrinkage matrix
        SIGMA_ZHY   : p x p covariance matrix
        PRECISION   : p x p precision matrix (from Theorem 1)
        VARIANCE    : p x p variance matrix
        sigma_sq    : per-asset variances
        pair_results: raw pairwise results
    """
    names = list(tick_data.keys())
    p = len(names)

    # Per-asset variances
    sigma_sq = {}
    for coin in names:
        df = tick_data[coin]
        T = df[time_col].iloc[-1] - df[time_col].iloc[0]
        ret = np.diff(df[price_col].values)
        sigma_sq[coin] = float(np.sum(ret**2) / T)

    # Pairwise estimates
    pair_results = {}
    for i, c1 in enumerate(names):
        for j, c2 in enumerate(names):
            if j <= i:
                continue
            res = estimate_pair(
                tick_data[c1], tick_data[c2],
                sigma1_sq=sigma_sq[c1],
                sigma2_sq=sigma_sq[c2],
                window_min=window_min,
                time_col=time_col,
                price_col=price_col)
            if res is not None:
                pair_results[(c1, c2)] = res

    # Assemble matrices
    RHO_ZHY   = np.eye(p)
    SIGMA_ZHY = np.diag([sigma_sq[c] for c in names])
    PRECISION  = np.full((p, p), np.inf)
    VARIANCE   = np.zeros((p, p))

    for i, c1 in enumerate(names):
        for j, c2 in enumerate(names):
            if i == j:
                continue
            key = (c1,c2) if (c1,c2) in pair_results else (c2,c1)
            if key not in pair_results:
                continue
            res = pair_results[key]
            RHO_ZHY[i,j]   = res['rho_est']
            SIGMA_ZHY[i,j]  = res['sigma_opt']
            PRECISION[i,j]  = res['precision']
            VARIANCE[i,j]   = res['variance']

    # Precision-weighted shrinkage (Paper 2)
    # Optimal element-wise shrinkage toward zero:
    # alpha_kl* = sigma_kl^2 / (sigma_kl^2 + Var(sigma_hat_kl | tau))
    RHO_SHRUNK = np.eye(p)
    for i in range(p):
        for j in range(p):
            if i == j:
                continue
            s12_sq = (RHO_ZHY[i,j]**2
                      * sigma_sq[names[i]] * sigma_sq[names[j]])
            var_ij = VARIANCE[i,j]
            if var_ij > 0 and np.isfinite(var_ij):
                alpha = s12_sq / (s12_sq + var_ij)
            else:
                alpha = 1.0
            RHO_SHRUNK[i,j] = alpha * RHO_ZHY[i,j]

    return {
        'names':        names,
        'RHO_ZHY':      RHO_ZHY,
        'RHO_SHRUNK':   RHO_SHRUNK,
        'SIGMA_ZHY':    SIGMA_ZHY,
        'PRECISION':    PRECISION,
        'VARIANCE':     VARIANCE,
        'sigma_sq':     sigma_sq,
        'pair_results': pair_results,
    }


def frobenius_error(R_est: np.ndarray, R_true: np.ndarray) -> float:
    """Frobenius norm of estimation error."""
    return float(np.sqrt(np.sum((R_est - R_true)**2)))


# ============================================================
# Quick demo
# ============================================================
if __name__ == '__main__':
    import numpy as np
    np.random.seed(42)

    # Simulate two assets
    rho_true = 0.7
    sigma1, sigma2 = 0.0003, 0.0006
    T_min = 480.0  # 8 hours

    # Correlated BM via Cholesky decomposition
    n_fine = 480000
    dt = T_min / n_fine
    t_fine = np.arange(n_fine) * dt
    SIG = np.array([[sigma1**2,               rho_true*sigma1*sigma2],
                    [rho_true*sigma1*sigma2,   sigma2**2            ]]) * dt
    L_chol = np.linalg.cholesky(SIG)
    Z = np.random.randn(n_fine, 2)
    dW = Z @ L_chol.T
    dW1, dW2 = dW[:, 0], dW[:, 1]
    P1 = np.cumsum(dW1)
    P2 = np.cumsum(dW2)

    # Poisson observations: asset 1 liquid (20/min), asset 2 illiquid (3/min)
    def poisson_obs(t_fine, P, rate, T):
        n_trades = np.random.poisson(rate * T)
        t_obs = np.sort(np.random.uniform(0, T, n_trades))
        idx = np.searchsorted(t_fine, t_obs, 'right') - 1
        idx = np.clip(idx, 0, len(P) - 1)
        return pd.DataFrame({'time_min': t_obs, 'log_price': P[idx]})

    df1 = poisson_obs(t_fine, P1, rate=20.0, T=T_min)
    df2 = poisson_obs(t_fine, P2, rate=3.0,  T=T_min)

    print(f"Asset 1: {len(df1)} trades")
    print(f"Asset 2: {len(df2)} trades")

    result = estimate_pair(df1, df2, window_min=30.0)

    print(f"\nTrue correlation:      {rho_true:.3f}")
    print(f"Estimated correlation: {result['rho_est']:.3f}")
    print(f"Exact variance:        {result['variance']:.2e}")
    print(f"Precision:             {result['precision']:.2e}")
    print(f"Overlapping pairs:     {result['n_overlaps']:,}")
