def sqrt(x):
    """for x>=0, return non-negative y such that y^2 = x"""
    estimate = x/2.0
    while True:
        newestimate = ((estimate+(x/estimate))/2.0)
        if newestimate == estimate:
            break
        estimate = newestimate
    return estimate

print("The answer is ", sqrt(2.0))
print("That answer squared is ", sqrt(2.0) * sqrt(2.0))
