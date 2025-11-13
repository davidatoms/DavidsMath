import matplotlib.pyplot as plt
import numpy as np

def continued_fraction(x, max_depth=20):
    """Compute the continued fraction expansion of x."""
    cf = []
    while x != 0 and len(cf) < max_depth:
        a = int(1 / x)
        cf.append(a)
        x = 1 / x - a
    return cf

def minkowski_question_mark(cf):
    """Evaluate the Minkowski question mark function from continued fraction."""
    total = 0.0
    exponent_sum = 0
    sign = 1
    for a in cf:
        exponent_sum += a
        total += sign * (1 / (2 ** exponent_sum))
        sign *= -1
    return total

# Generate x values and compute ?(x)
n_points = 1000
x_vals = np.linspace(0.001, 0.999, n_points)
y_vals = []

for x in x_vals:
    cf = continued_fraction(x)
    y = minkowski_question_mark(cf)
    y_vals.append(y)

# Plot
plt.figure(figsize=(8, 6))
plt.plot(x_vals, y_vals, lw=1, color="darkblue")
plt.title("Minkowski's Question Mark Function")
plt.xlabel("x")
plt.ylabel("?(x)")
plt.grid(True)
plt.tight_layout()
plt.show()
