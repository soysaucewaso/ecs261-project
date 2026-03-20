from module_ import PageTable

def test():
    pt = PageTable()
    pt.init();

    # pt.allocate(2,16)

    print(pt.translate(4096))
    print(pt.translate(0))
    print(pt.translate(5097))

    print("tested successfully")

if __name__ == "__main__":
    test()
