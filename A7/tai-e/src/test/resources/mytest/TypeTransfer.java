class TypeTransfer{

    int num;

    public static void main(String[] args){
        A a = new A();
        B b = new B();
        b.b_num = 1;
        TypeTransfer t = new TypeTransfer();
        a.set(3);
        int y = 2;
        t.num = y;
        int c = t.num + a.one();
        int d = t.num + a.a_num;

        b.b_num = a.a_num;

        a.a_num = a.one();
    }

}

class A{

    public int a_num;

    public int one(){
        return 1;
    }

    public void set(int num){
        this.a_num = num;
    }
}

class B{
    public int b_num;

}