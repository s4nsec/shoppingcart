import java.util.HashMap;

class Item{
    private Integer itemId;
    private Integer quantity;

    public Item(Integer itemId, Integer quantity){
        this.itemId = itemId;
        this.quantity = quantity;
    }

    public Integer getQuantity(){
        return this.quantity;
    }

    public Integer getItemId(){
        return this.itemId;
    }

}

class ShoppingCart{
    private Integer userId;
    private HashMap<Integer, Integer> items;

    public ShoppingCart(Integer userId){
        this.userId = userId;
        this.items = new HashMap<Integer, Integer>();
    }

    //@ requires itemId >= 0;
    //@ requires quantity >= 0;
    public void addItem(Integer itemId, Integer quantity){
        this.items.put(itemId, quantity);
    }
    public void removeItem(){
        // TODO
    }

}

public class Cart{
    public static void main(String[] args){
        Integer userId = 1;
        ShoppingCart shoppingCart = new ShoppingCart(userId);
        Item item2 = new Item(2, 4);
        Integer item2ItemId = -2;
        Integer item2Quantity = 4;
        shoppingCart.addItem(item2ItemId, item2Quantity);
    }
}
