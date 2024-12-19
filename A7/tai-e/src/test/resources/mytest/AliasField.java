class AliasField{
    public static void main(String[] args) {
        A a1 = new A();
        A a2 = new A();

        a1.f = 0;
        a2.f = 1;

        A b = a1;
        A c = a2;

        b.f = 2;
        c.f = 3;

        int x = a1.f;
        int y = a2.f;

        c = a1;

        c.f = 4;

        x = a1.f;

        y = a2.f;
    }
}

class A{
    int f;
}