#include <stdio.h>
#include <windows.h>
#include <stdlib.h>

void createWindow()
{
    BOOL freed = FreeConsole();
    AllocConsole();
}

void printAt(char c, int x, int y)
{
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    COORD p = {x,y};
    SetConsoleCursorPosition(h,p);
    putchar(c);
}

void clear()
{
    HANDLE hConsole = GetStdHandle(STD_OUTPUT_HANDLE);
    COORD coordScreen = { 0, 0 };    // home for the cursor 
    DWORD cCharsWritten;
    CONSOLE_SCREEN_BUFFER_INFO csbi; 
    DWORD dwConSize;
    if( !GetConsoleScreenBufferInfo( hConsole, &csbi ))
    {
      return;
    }

    dwConSize = csbi.dwSize.X * csbi.dwSize.Y;

   // Fill the entire screen with blanks.

   if( !FillConsoleOutputCharacter( hConsole,        // Handle to console screen buffer 
                                    (TCHAR) ' ',     // Character to write to the buffer
                                    dwConSize,       // Number of cells to write 
                                    coordScreen,     // Coordinates of first cell 
                                    &cCharsWritten ))// Receive number of characters written
   {
      return;
   }

   // Get the current text attribute.

   if( !GetConsoleScreenBufferInfo( hConsole, &csbi ))
   {
      return;
   }

   // Set the buffer's attributes accordingly.

   if( !FillConsoleOutputAttribute( hConsole,         // Handle to console screen buffer 
                                    csbi.wAttributes, // Character attributes to use
                                    dwConSize,        // Number of cells to set attribute 
                                    coordScreen,      // Coordinates of first cell 
                                    &cCharsWritten )) // Receive number of characters written
   {
      return;
   }

   // Put the cursor at its home coordinates.

   SetConsoleCursorPosition( hConsole, coordScreen );

}