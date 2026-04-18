"""
Plot Results: Precision-Weighted ZHY Covariance Estimation
===========================================================
Generates the six-panel comparison figure for the crypto demo.
Run after crypto_demo.py.
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec

names = ['BTC', 'ETH', 'SOL', 'LINK', 'ADA']
n = len(names)

RHO_TRUE   = np.load('/tmp/RHO_TRUE.npy')
RHO_NAIVE  = np.load('/tmp/RHO_NAIVE.npy')
RHO_ZHY    = np.load('/tmp/RHO_ZHY.npy')
RHO_SHRUNK = np.load('/tmp/RHO_SHRUNK.npy')
PRECISION  = np.load('/tmp/PRECISION.npy')

def frob(A, B):
    return float(np.sqrt(np.sum((A - B)**2)))

err_naive  = frob(RHO_NAIVE,  RHO_TRUE)
err_zhy    = frob(RHO_ZHY,    RHO_TRUE)
err_shrunk = frob(RHO_SHRUNK, RHO_TRUE)

plt.rcParams.update({
    'font.family': 'serif',
    'font.size': 9.5,
    'axes.spines.top': False,
    'axes.spines.right': False,
})

fig = plt.figure(figsize=(14, 9))
gs  = gridspec.GridSpec(2, 3, figure=fig, hspace=0.5, wspace=0.32)

vmin, vmax, cmap = 0.3, 1.0, 'Blues'

def heatmap(ax, R, title, err=None):
    im = ax.imshow(R, cmap=cmap, vmin=vmin, vmax=vmax, aspect='auto')
    ax.set_xticks(range(n)); ax.set_yticks(range(n))
    ax.set_xticklabels(names, fontsize=8.5)
    ax.set_yticklabels(names, fontsize=8.5)
    for i in range(n):
        for j in range(n):
            col = 'white' if R[i,j] > 0.72 else '#222'
            ax.text(j, i, f'{R[i,j]:.2f}',
                    ha='center', va='center',
                    fontsize=8, color=col)
    t = title
    if err is not None:
        t += f'\n$\\|\\hat{{\\rho}} - \\rho_0\\|_F = {err:.4f}$'
    ax.set_title(t, fontsize=10, pad=7)
    return im

ax1 = fig.add_subplot(gs[0, 0])
ax2 = fig.add_subplot(gs[0, 1])
ax3 = fig.add_subplot(gs[0, 2])
ax4 = fig.add_subplot(gs[1, 0])
ax5 = fig.add_subplot(gs[1, 1])
ax6 = fig.add_subplot(gs[1, 2])

heatmap(ax1, RHO_TRUE,   'True Correlation $\\rho_0$')
heatmap(ax2, RHO_NAIVE,  'Naive 5-min Synchronised',         err_naive)
im = heatmap(ax3, RHO_ZHY,
             'Optimal ZHY Estimator\n(Thesis Theorem 1)',     err_zhy)
heatmap(ax4, RHO_SHRUNK,
        'Precision-Weighted\nShrinkage (Paper 2)',            err_shrunk)

# Precision heatmap
P_log = np.where(
    (PRECISION > 0) & np.isfinite(PRECISION),
    np.log10(np.where(PRECISION > 0, PRECISION, 1)),
    np.nan)
np.fill_diagonal(P_log, np.nan)
im5 = ax5.imshow(P_log, cmap='RdYlGn', aspect='auto')
ax5.set_xticks(range(n)); ax5.set_yticks(range(n))
ax5.set_xticklabels(names, fontsize=8.5)
ax5.set_yticklabels(names, fontsize=8.5)
for i in range(n):
    for j in range(n):
        if i != j and np.isfinite(P_log[i, j]):
            ax5.text(j, i, f'{P_log[i,j]:.1f}',
                     ha='center', va='center', fontsize=8.5)
ax5.set_title('$\\log_{10}$(Precision per pair)\nfrom Theorem 1',
              fontsize=10, pad=7)
plt.colorbar(im5, ax=ax5, shrink=0.78, pad=0.03)

# Error bar chart
methods = ['Naive\n5-min', 'Optimal\nZHY', 'Precision-\nWeighted\nShrinkage']
errors  = [err_naive, err_zhy, err_shrunk]
colors  = ['#c0392b', '#2980b9', '#27ae60']
bars = ax6.bar(methods, errors, color=colors, width=0.45,
               alpha=0.88, edgecolor='white', linewidth=1.0)
for bar, e in zip(bars, errors):
    ax6.text(bar.get_x() + bar.get_width()/2.,
             bar.get_height() + 0.002,
             f'{e:.4f}', ha='center', va='bottom',
             fontsize=9, fontweight='bold')
ax6.set_ylabel('Frobenius Error $\\|\\hat{\\rho} - \\rho_0\\|_F$',
               fontsize=9.5)
ax6.set_title('Estimation Error\nvs True Correlation', fontsize=10, pad=7)
ax6.set_ylim(0, max(errors) * 1.28)
ax6.yaxis.grid(True, alpha=0.25, linewidth=0.6)
ax6.set_axisbelow(True)

# Improvement arrow
ax6.annotate('', xy=(1, err_zhy + 0.002),
             xytext=(0, err_naive + 0.002),
             arrowprops=dict(arrowstyle='<->', color='gray', lw=1.2))
ax6.text(0.5, (err_zhy + err_naive)/2 + 0.03,
         f'{err_naive/err_zhy:.1f}x better',
         ha='center', va='bottom', fontsize=8.5, color='gray')

# Shared colourbar
cbar_ax = fig.add_axes([0.93, 0.52, 0.012, 0.38])
cb = plt.colorbar(im, cax=cbar_ax)
cb.set_label('Correlation', fontsize=9)

fig.text(0.5, 0.005,
         'Trade rates:  BTC 50/min  ·  ETH 35/min  ·  '
         'SOL 15/min  ·  LINK 5/min  ·  ADA 3/min',
         ha='center', fontsize=8, color='#555', style='italic')

fig.suptitle(
    'Precision-Weighted ZHY Covariance Estimation  —  Five Crypto Assets\n'
    'Exact variance from Theorem 1 drives element-wise shrinkage; '
    'liquid pairs trusted more, illiquid pairs shrunk more',
    fontsize=10.5, y=0.995)

plt.savefig('crypto_results.pdf', bbox_inches='tight',
            dpi=300, facecolor='white')
plt.savefig('crypto_results.png', bbox_inches='tight',
            dpi=300, facecolor='white')
print("Saved crypto_results.pdf and crypto_results.png")
