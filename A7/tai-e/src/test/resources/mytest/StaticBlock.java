class StaticBlock {
    static int one = 1;
    static int two;

    static {
        one = 1;
        two = 2;
    }

    public static void main(String[] args) {
        int a = StaticBlock.one;
        int b = StaticBlock.two;
        int c = a + b;

    }
}