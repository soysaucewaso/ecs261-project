from module_ import PageTable

def test():
    pt = PageTable()

    # pt.allocate(2,16)

    print(pt.translate(2))

    print("tested successfully")

if __name__ == "__main__":
    test()