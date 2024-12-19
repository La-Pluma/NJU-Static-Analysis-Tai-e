class ObjSen{
    public static void main(String[] args){
        A a1 = new A();
        A a2 = new A();
        B b1 = new B();
        B b2 = new B();

        a1.set(b1);
        a2.set(b2);

        B x = a1.get();

    }
}

class A{
    B f;

    public void set(B b){
        this.doset(b);
    }
    public void doset(B b){
        this.f = b;
    }
    public B get(){
        return this.f;
    }
}

class B{
    int num;
}