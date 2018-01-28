def sqrt(number):
    estimate = number/2
    while True:
        newestimate = ((estimate+(number/estimate))/2.0)
        if newestimate == estimate:
            break
        estimate = newestimate
    return estimate

print(sqrt(19.0))

