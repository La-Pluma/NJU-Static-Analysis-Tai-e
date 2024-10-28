
// ./gradlew clean run --args=" -cp src/test/resources/dataflow/livevar -m ArrayDef"
class ArrayDef {

    int sum(int arr[]) {
        int[] copy = new int[arr.length];
        int result = 0;
        for (int i = 0; i < arr.length; i++) {
            copy[i] = arr[i];
            result += arr[i];
        }
        return result;
    }

}